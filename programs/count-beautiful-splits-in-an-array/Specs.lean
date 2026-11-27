import Aegis.BeautifulSplits.Code.Funs

/-!
# Specifications of `Aegis.BeautifulSplits.beautiful_splits`

LeetCode problem `count-beautiful-splits-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.BeautifulSplits

namespace AegisSpec.BeautifulSplits

def entry (nums : Slice Std.I64) (k : ℕ) : ℤ := (nums.val.getD k default).val

abbrev condA (nums : Slice Std.I64) (i j : ℕ) : Prop :=
  i ≤ j - i ∧ ∀ k, k < i → entry nums k = entry nums (i + k)

abbrev condB (nums : Slice Std.I64) (i j : ℕ) : Prop :=
  j - i ≤ nums.val.length - j ∧ ∀ k, k < j - i → entry nums (i + k) = entry nums (j + k)

abbrev Beautiful (nums : Slice Std.I64) (i j : ℕ) : Prop :=
  1 ≤ i ∧ i < j ∧ j < nums.val.length ∧ (condA nums i j ∨ condB nums i j)

def beautifulPairs (nums : Slice Std.I64) : Finset (ℕ × ℕ) :=
  ((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
    (fun p => Beautiful nums p.1 p.2)

def beautifulCount (nums : Slice Std.I64) : ℕ := (beautifulPairs nums).card

def bPairs (nums : Slice Std.I64) : Finset (ℕ × ℕ) :=
  ((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
    (fun p => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < nums.val.length ∧ condB nums p.1 p.2)

def bCount (nums : Slice Std.I64) : ℕ := (bPairs nums).card

def allSplitPairs (nums : Slice Std.I64) : Finset (ℕ × ℕ) :=
  ((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
    (fun p => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < nums.val.length)

def IsExt (nums ext : Slice Std.I64) (x : ℤ) : Prop :=
  ext.val.length = nums.val.length + 1 ∧
    (∀ k, k < nums.val.length → entry ext k = entry nums k) ∧
      entry ext nums.val.length = x

def IsPrefixSlice (pre nums : Slice Std.I64) (k : ℕ) : Prop :=
  pre.val.length = k ∧ ∀ i, i < k → entry pre i = entry nums i

/-- Let n = len(nums). For integers i and j, call the split (i,j) beautiful exactly when 1 <= i < j < n and either (A) i <= j - i and for every k with 0 <= k < i, nums[k] = nums[i+k], or (B) j - i <= n - j and for every k with 0 <= k < j - i, nums[i+k] = nums[j+k]. The function returns a result r and r equals the number of beautiful pairs (i,j).
  Preconditions: 1 <= len(nums) <= 5000 and for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50) :
    ∃ r, beautiful_splits nums = ok r ∧ r.val = (beautifulCount nums : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50), ∃ r, beautiful_splits nums = ok r ∧ r.val = (beautifulCount nums : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, access out of bounds, or panic.
  Preconditions: 1 <= len(nums) <= 5000 and for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50) :
    ∃ r, beautiful_splits nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50), ∃ r, beautiful_splits nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: 1 <= len(nums) <= 5000 and for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50) :
    ∀ r, beautiful_splits nums = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50), ∀ r, beautiful_splits nums = ok r → 0 ≤ r.val) := by
  sorry

/-- Let N be the number of integer pairs (i,j) such that 1 <= i < j < len(nums). Whenever the function returns a result r, r <= N.
  Preconditions: 1 <= len(nums) <= 5000 and for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50) :
    ∀ r, beautiful_splits nums = ok r → r.val ≤ ((allSplitPairs nums).card : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50), ∀ r, beautiful_splits nums = ok r → r.val ≤ ((allSplitPairs nums).card : ℤ)) := by
  sorry

/-- If len(nums) <= 2, then the function returns a result r and r = 0.
  Preconditions: 1 <= len(nums) <= 5000 and for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (hshort : nums.val.length ≤ 2) :
    ∃ r, beautiful_splits nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (hshort : nums.val.length ≤ 2), ∃ r, beautiful_splits nums = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r, and r = 1 if nums[0] = nums[1] or nums[1] = nums[2], and r = 0 otherwise.
  Preconditions: len(nums) = 3 and 0 <= nums[0], nums[1], nums[2] <= 50. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : nums.val.length = 3)
    (h0 : 0 ≤ entry nums 0 ∧ entry nums 0 ≤ 50)
    (h1 : 0 ≤ entry nums 1 ∧ entry nums 1 ≤ 50)
    (h2 : 0 ≤ entry nums 2 ∧ entry nums 2 ≤ 50) :
    ∃ r, beautiful_splits nums = ok r ∧
      r.val = (if entry nums 0 = entry nums 1 ∨ entry nums 1 = entry nums 2 then (1 : ℤ) else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 3)
    (h0 : 0 ≤ entry nums 0 ∧ entry nums 0 ≤ 50)
    (h1 : 0 ≤ entry nums 1 ∧ entry nums 1 ≤ 50)
    (h2 : 0 ≤ entry nums 2 ∧ entry nums 2 ≤ 50), ∃ r, beautiful_splits nums = ok r ∧
      r.val = (if entry nums 0 = entry nums 1 ∨ entry nums 1 = entry nums 2 then (1 : ℤ) else 0)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result r, r equals the number of integer pairs (i,j) such that 1 <= i < j < n, j - i <= n - j, and for every k with 0 <= k < j - i, nums[i+k] = nums[j+k].
  Preconditions: 1 <= len(nums) <= 5000, for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50, and for every i with 1 <= i < len(nums), nums[0] != nums[i]. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (hfresh : ∀ i, 1 ≤ i → i < nums.val.length → entry nums 0 ≠ entry nums i) :
    ∀ r, beautiful_splits nums = ok r → r.val = (bCount nums : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (hfresh : ∀ i, 1 ≤ i → i < nums.val.length → entry nums 0 ≠ entry nums i), ∀ r, beautiful_splits nums = ok r → r.val = (bCount nums : ℤ)) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: 1 <= len(nums) <= 5000, for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50, and for every p,q with 0 <= p < q < len(nums), nums[p] != nums[q]. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (hnd : ∀ p q, p < q → q < nums.val.length → entry nums p ≠ entry nums q) :
    ∃ r, beautiful_splits nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (hnd : ∀ p q, p < q → q < nums.val.length → entry nums p ≠ entry nums q), ∃ r, beautiful_splits nums = ok r ∧ r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if r > 0 then there exist integers i and j with 1 <= i < j < len(nums) such that either (i <= j - i and for every k with 0 <= k < i, nums[k] = nums[i+k]) or (j - i <= len(nums) - j and for every k with 0 <= k < j - i, nums[i+k] = nums[j+k]).
  Preconditions: 1 <= len(nums) <= 5000 and for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50) :
    ∀ r, beautiful_splits nums = ok r → 0 < r.val → ∃ i j, Beautiful nums i j := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50), ∀ r, beautiful_splits nums = ok r → 0 < r.val → ∃ i j, Beautiful nums i j) := by
  sorry

/-- If beautiful_splits(nums) returns r and beautiful_splits(alt) returns r_alt, then r = r_alt.
  Preconditions: 1 <= len(nums) <= 5000, for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50, and alt is an array such that len(alt) = len(nums), for every k with 0 <= k < len(alt), 0 <= alt[k] <= 50, and for every p,q with 0 <= p < len(nums) and 0 <= q < len(nums), nums[p] = nums[q] if and only if alt[p] = alt[q]. -/
theorem spec_10 (nums alt : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (halt_len : alt.val.length = nums.val.length)
    (halt_val : ∀ (k : ℕ), k < alt.val.length → 0 ≤ entry alt k ∧ entry alt k ≤ 50)
    (hpat : ∀ p q, p < nums.val.length → q < nums.val.length →
      (entry nums p = entry nums q ↔ entry alt p = entry alt q)) :
    ∀ r r_alt, beautiful_splits nums = ok r → beautiful_splits alt = ok r_alt → r = r_alt := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums alt : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (halt_len : alt.val.length = nums.val.length)
    (halt_val : ∀ (k : ℕ), k < alt.val.length → 0 ≤ entry alt k ∧ entry alt k ≤ 50)
    (hpat : ∀ p q, p < nums.val.length → q < nums.val.length →
      (entry nums p = entry nums q ↔ entry alt p = entry alt q)), ∀ r r_alt, beautiful_splits nums = ok r → beautiful_splits alt = ok r_alt → r = r_alt) := by
  sorry

/-- For every integer x with 0 <= x <= 50, let ext be the array of length len(nums)+1 such that ext[k] = nums[k] for 0 <= k < len(nums) and ext[len(nums)] = x. Whenever beautiful_splits(nums) returns r and beautiful_splits(ext) returns r_ext, r_ext >= r.
  Preconditions: 1 <= len(nums) <= 4999 and for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 4999)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50) :
    ∀ (x : ℤ), 0 ≤ x → x ≤ 50 → ∀ ext : Slice Std.I64, IsExt nums ext x →
      ∀ r r_ext, beautiful_splits nums = ok r → beautiful_splits ext = ok r_ext → r ≤ r_ext := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 4999)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50), ∀ (x : ℤ), 0 ≤ x → x ≤ 50 → ∀ ext : Slice Std.I64, IsExt nums ext x →
      ∀ r r_ext, beautiful_splits nums = ok r → beautiful_splits ext = ok r_ext → r ≤ r_ext) := by
  sorry

/-- For every integer x with 0 <= x <= 50, let ext be the array of length len(nums)+1 such that ext[k] = nums[k] for 0 <= k < len(nums) and ext[len(nums)] = x. Whenever beautiful_splits(nums) returns r and beautiful_splits(ext) returns r_ext, r_ext - r <= 2*(len(nums)-1).
  Preconditions: 1 <= len(nums) <= 4999 and for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 4999)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50) :
    ∀ (x : ℤ), 0 ≤ x → x ≤ 50 → ∀ ext : Slice Std.I64, IsExt nums ext x →
      ∀ r r_ext, beautiful_splits nums = ok r → beautiful_splits ext = ok r_ext →
        r_ext - r ≤ 2 * ((nums.val.length : ℤ) - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 4999)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50), ∀ (x : ℤ), 0 ≤ x → x ≤ 50 → ∀ ext : Slice Std.I64, IsExt nums ext x →
      ∀ r r_ext, beautiful_splits nums = ok r → beautiful_splits ext = ok r_ext →
        r_ext - r ≤ 2 * ((nums.val.length : ℤ) - 1)) := by
  sorry

/-- The function returns a result r and r >= 1.
  Preconditions: 1 <= len(nums) <= 5000, for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50, len(nums) >= 3, and (nums[0] = nums[1] or nums[len(nums)-2] = nums[len(nums)-1]). -/
theorem spec_13 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (h3 : 3 ≤ nums.val.length)
    (hrep : entry nums 0 = entry nums 1 ∨
      entry nums (nums.val.length - 2) = entry nums (nums.val.length - 1)) :
    ∃ r, beautiful_splits nums = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (h3 : 3 ≤ nums.val.length)
    (hrep : entry nums 0 = entry nums 1 ∨
      entry nums (nums.val.length - 2) = entry nums (nums.val.length - 1)), ∃ r, beautiful_splits nums = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- Let pre be the slice nums[0..k). If beautiful_splits(pre) returns r_pre and beautiful_splits(nums) returns r, then r_pre <= r.
  Preconditions: 1 <= len(nums) <= 5000, for every k with 0 <= k < len(nums), 0 <= nums[k] <= 50, and 1 <= k <= len(nums). -/
theorem spec_14 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ nums.val.length)
    (pre : Slice Std.I64) (hpre : IsPrefixSlice pre nums k) :
    ∀ r_pre r, beautiful_splits pre = ok r_pre → beautiful_splits nums = ok r → r_pre ≤ r := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 5000)
    (hval : ∀ (k : ℕ), k < nums.val.length → 0 ≤ entry nums k ∧ entry nums k ≤ 50)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ nums.val.length)
    (pre : Slice Std.I64) (hpre : IsPrefixSlice pre nums k), ∀ r_pre r, beautiful_splits pre = ok r_pre → beautiful_splits nums = ok r → r_pre ≤ r) := by
  sorry

end AegisSpec.BeautifulSplits
