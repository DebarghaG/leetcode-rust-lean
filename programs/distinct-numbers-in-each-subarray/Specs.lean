import Aegis.DistinctNumbers.Code.Funs

/-!
# Specifications of `Aegis.DistinctNumbers.distinct_numbers`

LeetCode problem `distinct-numbers-in-each-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.DistinctNumbers

  namespace AegisSpec.DistinctNumbers

  def vals (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

  def numDistinct (l : List Std.I64) : ℕ := (vals l).toFinset.card

  def window (nums : Slice Std.I64) (i k : ℕ) : List Std.I64 :=
    (nums.val.drop i).take k

  def windowDistinct (nums : Slice Std.I64) (i k : ℕ) : ℕ :=
    numDistinct (window nums i k)

  def inAt (nums : Slice Std.I64) (i : ℕ) : Option ℤ :=
    (nums.val[i]?).map (fun x => x.val)

  def outAt (r : alloc.vec.Vec Std.I64) (i : ℕ) : Option ℤ :=
    (r.val[i]?).map (fun x => x.val)

  def ValuesInRange (l : List Std.I64) (lo hi : ℤ) : Prop :=
    ∀ v ∈ vals l, lo ≤ v ∧ v ≤ hi

  def PairwiseDistinct (l : List Std.I64) : Prop := (vals l).Nodup

  def AllEqual (l : List Std.I64) : Prop :=
    ∀ x ∈ vals l, ∀ y ∈ vals l, x = y

  def SameMultiplicity (l₁ l₂ : List Std.I64) : Prop :=
    ∀ v : ℤ, (vals l₁).countP (fun x => decide (x = v)) =
      (vals l₂).countP (fun x => decide (x = v))

  /-- Whenever the function returns a result r, len(r) = len(nums) - k + 1, and for every i with 0 <= i <= len(nums) - k, r[i] equals the number of distinct values in the contiguous length-k window nums[i], nums[i+1], ..., nums[i+k-1]; formally r[i] = |{ nums[j] | i <= j < i+k }|. All indices are 0-based, and each window is nonempty because k >= 1.
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∀ r, distinct_numbers nums k = ok r →
        r.val.length = nums.val.length - k.val.toNat + 1 ∧
        ∀ i, i ≤ nums.val.length - k.val.toNat →
          outAt r i = some ↑(windowDistinct nums i k.val.toNat) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∀ r, distinct_numbers nums k = ok r →
          r.val.length = nums.val.length - k.val.toNat + 1 ∧
          ∀ i, i ≤ nums.val.length - k.val.toNat →
            outAt r i = some ↑(windowDistinct nums i k.val.toNat)) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, out-of-bounds, or panic) for any input satisfying the preconditions.
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∃ r, distinct_numbers nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∃ r, distinct_numbers nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 1 <= r[i] <= k. Each entry is therefore a valid distinct-count for a window of exactly k elements and fits in i64.
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∀ r, distinct_numbers nums k = ok r →
        ∀ i, i < r.val.length →
          ∃ v : ℤ, outAt r i = some v ∧ 1 ≤ v ∧ v ≤ k.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∀ r, distinct_numbers nums k = ok r →
          ∀ i, i < r.val.length →
            ∃ v : ℤ, outAt r i = some v ∧ 1 ≤ v ∧ v ≤ k.val) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums), and for every i with 0 <= i < len(nums), r[i] = 1.
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; k = 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk : k.val = 1)
      (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∀ r, distinct_numbers nums k = ok r →
        r.val.length = nums.val.length ∧
        ∀ i, i < nums.val.length → outAt r i = some 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk : k.val = 1)
        (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∀ r, distinct_numbers nums k = ok r →
          r.val.length = nums.val.length ∧
          ∀ i, i < nums.val.length → outAt r i = some 1) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 1, and r[0] equals the number of distinct values in the whole slice nums, i.e. r[0] = |{ nums[j] | 0 <= j < len(nums) }|.
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; k = len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk : k.val = (nums.val.length : ℤ))
      (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∀ r, distinct_numbers nums k = ok r →
        r.val.length = 1 ∧
        outAt r 0 = some ↑(numDistinct nums.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk : k.val = (nums.val.length : ℤ))
        (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∀ r, distinct_numbers nums k = ok r →
          r.val.length = 1 ∧
          outAt r 0 = some ↑(numDistinct nums.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] = 1.
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and for every i, j with 0 <= i, j < len(nums), nums[i] = nums[j]. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000)
      (hconst : AllEqual nums.val) :
      ∀ r, distinct_numbers nums k = ok r →
        ∀ i, i < r.val.length → outAt r i = some 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000)
        (hconst : AllEqual nums.val), ∀ r, distinct_numbers nums k = ok r →
          ∀ i, i < r.val.length → outAt r i = some 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] = k.
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; and for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000)
      (hnd : PairwiseDistinct nums.val) :
      ∀ r, distinct_numbers nums k = ok r →
        ∀ i, i < r.val.length → outAt r i = some k.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000)
        (hnd : PairwiseDistinct nums.val), ∀ r, distinct_numbers nums k = ok r →
          ∀ i, i < r.val.length → outAt r i = some k.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i <= len(nums) - k, r[i] = k if and only if the k elements nums[i], nums[i+1], ..., nums[i+k-1] are pairwise distinct (equivalently, no value occurs more than once in that window).
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∀ r, distinct_numbers nums k = ok r →
        ∀ i, i ≤ nums.val.length - k.val.toNat →
          (outAt r i = some k.val ↔
            PairwiseDistinct (window nums i k.val.toNat)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∀ r, distinct_numbers nums k = ok r →
          ∀ i, i ≤ nums.val.length - k.val.toNat →
            (outAt r i = some k.val ↔
              PairwiseDistinct (window nums i k.val.toNat))) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i <= len(nums) - k, r[i] = 1 if and only if all k elements nums[i], nums[i+1], ..., nums[i+k-1] are equal to one another.
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∀ r, distinct_numbers nums k = ok r →
        ∀ i, i ≤ nums.val.length - k.val.toNat →
          (outAt r i = some 1 ↔ AllEqual (window nums i k.val.toNat)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∀ r, distinct_numbers nums k = ok r →
          ∀ i, i ≤ nums.val.length - k.val.toNat →
            (outAt r i = some 1 ↔ AllEqual (window nums i k.val.toNat))) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 1 <= i < len(r), |r[i] - r[i-1]| <= 1. Consecutive windows have distinct counts differing by at most one.
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∀ r, distinct_numbers nums k = ok r →
        ∀ i, 1 ≤ i → i < r.val.length →
          ∃ a b : ℤ, outAt r i = some a ∧ outAt r (i - 1) = some b ∧ |a - b| ≤ 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∀ r, distinct_numbers nums k = ok r →
          ∀ i, 1 ≤ i → i < r.val.length →
            ∃ a b : ℤ, outAt r i = some a ∧ outAt r (i - 1) = some b ∧ |a - b| ≤ 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums) - k, if nums[i] = nums[i+k], then r[i] = r[i+1].
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∀ r, distinct_numbers nums k = ok r →
        ∀ i, i < nums.val.length - k.val.toNat →
          inAt nums i = inAt nums (i + k.val.toNat) →
          outAt r i = outAt r (i + 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∀ r, distinct_numbers nums k = ok r →
          ∀ i, i < nums.val.length - k.val.toNat →
            inAt nums i = inAt nums (i + k.val.toNat) →
            outAt r i = outAt r (i + 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] <= |{ nums[j] | 0 <= j < len(nums) }|. No window can contain more distinct values than the whole array.
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∀ r, distinct_numbers nums k = ok r →
        ∀ i, i < r.val.length →
          ∃ v : ℤ, outAt r i = some v ∧ v ≤ ↑(numDistinct nums.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∀ r, distinct_numbers nums k = ok r →
          ∀ i, i < r.val.length →
            ∃ v : ℤ, outAt r i = some v ∧ v ≤ ↑(numDistinct nums.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of valid window starts i and j with 0 <= i, j <= len(nums) - k, if every integer value occurs with the same multiplicity in nums[i], nums[i+1], ..., nums[i+k-1] as in nums[j], nums[j+1], ..., nums[j+k-1], then r[i] = r[j].
    Preconditions: nums is a slice of i64 with len(nums) >= 1; k is an i64; 1 <= k <= len(nums); len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
      (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
      (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
      (hval : ValuesInRange nums.val 1 100000) :
      ∀ r, distinct_numbers nums k = ok r →
        ∀ i j, i ≤ nums.val.length - k.val.toNat →
          j ≤ nums.val.length - k.val.toNat →
          SameMultiplicity (window nums i k.val.toNat) (window nums j k.val.toNat) →
          outAt r i = outAt r j := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
        (hk2 : k.val ≤ (nums.val.length : ℤ)) (hlen : nums.val.length ≤ 100000)
        (hval : ValuesInRange nums.val 1 100000), ∀ r, distinct_numbers nums k = ok r →
          ∀ i j, i ≤ nums.val.length - k.val.toNat →
            j ≤ nums.val.length - k.val.toNat →
            SameMultiplicity (window nums i k.val.toNat) (window nums j k.val.toNat) →
            outAt r i = outAt r j) := by
    sorry

  end AegisSpec.DistinctNumbers
