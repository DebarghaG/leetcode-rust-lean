import Aegis.CountBadPairs.Code.Funs

/-!
# Specifications of `Aegis.CountBadPairs.count_bad_pairs`

LeetCode problem `count-number-of-bad-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountBadPairs

  def elemAt (nums : Slice I64) (i : Nat) : Int :=
    (nums.val[i]?).elim 0 (fun x => x.val)

  def sliceLen (nums : Slice I64) : Nat := nums.val.length

  def keyAt (nums : Slice I64) (i : Nat) : Int := elemAt nums i - (i : Int)

  abbrev isBadPair (nums : Slice I64) (i j : Nat) : Prop :=
    i < j ∧ (j : Int) - (i : Int) ≠ elemAt nums j - elemAt nums i

  abbrev isGoodPair (nums : Slice I64) (i j : Nat) : Prop :=
    i < j ∧ keyAt nums i = keyAt nums j

  def totalPairs (nums : Slice I64) : Nat :=
    sliceLen nums * (sliceLen nums - 1) / 2

  def badPairCount (nums : Slice I64) : Nat :=
    (((Finset.range (sliceLen nums)).product (Finset.range (sliceLen nums))).filter
      (fun (p : Nat × Nat) => isBadPair nums p.1 p.2)).card

  def goodPairCount (nums : Slice I64) : Nat :=
    (((Finset.range (sliceLen nums)).product (Finset.range (sliceLen nums))).filter
      (fun (p : Nat × Nat) => isGoodPair nums p.1 p.2)).card

  def keyMult (nums : Slice I64) (v : Int) : Nat :=
    ((Finset.range (sliceLen nums)).filter (fun i => keyAt nums i = v)).card

  def goodPairSum (nums : Slice I64) : Nat :=
    ((Finset.range (sliceLen nums)).image (keyAt nums)).sum
      (fun v => keyMult nums v * (keyMult nums v - 1) / 2)

  /-- Whenever the function returns a result r, r is the number of pairs (i, j) of indices such that 0 <= i < j < len(nums) and j - i != nums[j] - nums[i], where nums[k] denotes the integer value of the k-th I64 element and the subtraction in the comparison is mathematical integer subtraction. Each unordered pair of distinct indices is counted exactly once.
    Preconditions: nums is a slice of Std.I64 with 1 <= len(nums) <= 100000, and nums[i] is an integer satisfying 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums). -/
  theorem spec_1 (nums : Slice I64)
      (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
      (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000) :
      ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
        r.val = (badPairCount nums : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
        (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000), ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
          r.val = (badPairCount nums : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: nums is a slice of Std.I64 with 1 <= len(nums) <= 100000, and nums[i] is an integer satisfying 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums). -/
  theorem spec_2 (nums : Slice I64)
      (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
      (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000) :
      ∃ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
        (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000), ∃ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: nums is a slice of Std.I64 with 1 <= len(nums) <= 100000, and nums[i] is an integer satisfying 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums). -/
  theorem spec_3 (nums : Slice I64)
      (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
      (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000) :
      ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
        (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000), ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(nums) * (len(nums) - 1) / 2.
    Preconditions: nums is a slice of Std.I64 with 1 <= len(nums) <= 100000, and nums[i] is an integer satisfying 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums). -/
  theorem spec_4 (nums : Slice I64)
      (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
      (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000) :
      ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
        r.val ≤ ((sliceLen nums : Int) * ((sliceLen nums : Int) - 1)) / 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
        (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000), ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
          r.val ≤ ((sliceLen nums : Int) * ((sliceLen nums : Int) - 1)) / 2) := by
    sorry

  /-- Whenever the function returns a result r, let n = len(nums) and let g be the number of pairs (i, j) with 0 <= i < j < n and nums[j] - j = nums[i] - i, where nums[k] denotes the integer value of the k-th I64 element. Then r = n * (n - 1) / 2 - g.
    Preconditions: nums is a slice of Std.I64 with 1 <= len(nums) <= 100000, and nums[i] is an integer satisfying 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums). -/
  theorem spec_5 (nums : Slice I64)
      (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
      (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000) :
      ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
        r.val = (totalPairs nums : Int) - (goodPairCount nums : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
        (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000), ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
          r.val = (totalPairs nums : Int) - (goodPairCount nums : Int)) := by
    sorry

  /-- Whenever the function returns a result r, let n = len(nums) and, for each integer v, let f(v) be the number of indices i with 0 <= i < n and nums[i] - i = v, where nums[k] denotes the integer value of the k-th I64 element. Then r = n * (n - 1) / 2 - sum_v f(v) * (f(v) - 1) / 2, where the sum is over the finitely many integers v with f(v) > 0.
    Preconditions: nums is a slice of Std.I64 with 1 <= len(nums) <= 100000, and nums[i] is an integer satisfying 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums). -/
  theorem spec_6 (nums : Slice I64)
      (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
      (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000) :
      ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
        r.val = (totalPairs nums : Int) - (goodPairSum nums : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
        (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000), ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
          r.val = (totalPairs nums : Int) - (goodPairSum nums : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there exists an integer c such that nums[i] - i = c for every index i with 0 <= i < len(nums), where nums[k] denotes the integer value of the k-th I64 element.
    Preconditions: nums is a slice of Std.I64 with 1 <= len(nums) <= 100000, and nums[i] is an integer satisfying 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums). -/
  theorem spec_7 (nums : Slice I64)
      (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
      (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000) :
      ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
        (r.val = 0 ↔ ∃ c : Int, ∀ i, i < sliceLen nums → keyAt nums i = c) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
        (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000), ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
          (r.val = 0 ↔ ∃ c : Int, ∀ i, i < sliceLen nums → keyAt nums i = c)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) * (len(nums) - 1) / 2 if and only if nums[i] - i != nums[j] - j for every 0 <= i < j < len(nums), where nums[k] denotes the integer value of the k-th I64 element.
    Preconditions: nums is a slice of Std.I64 with 1 <= len(nums) <= 100000, and nums[i] is an integer satisfying 1 <= nums[i] <= 1000000000 for every 0 <= i < len(nums). -/
  theorem spec_8 (nums : Slice I64)
      (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
      (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000) :
      ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
        (r.val = (totalPairs nums : Int) ↔
          ∀ i j, i < j → j < sliceLen nums → keyAt nums i ≠ keyAt nums j) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
        (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000), ∀ r, Aegis.CountBadPairs.count_bad_pairs nums = ok r →
          (r.val = (totalPairs nums : Int) ↔
            ∀ i j, i < j → j < sliceLen nums → keyAt nums i ≠ keyAt nums j)) := by
    sorry

  /-- If the function returns r on input nums and r' on input nums', then r = r'.
    Preconditions: nums and nums' are slices of Std.I64, both satisfy the problem constraints: 1 <= len(nums) = len(nums') <= 100000, and for every i with 0 <= i < len(nums), both 1 <= nums[i] <= 1000000000 and 1 <= nums'[i] <= 1000000000. There exists an integer c such that nums'[i] = nums[i] + c for every 0 <= i < len(nums), with nums[i] and nums'[i] denoting mathematical integer values. -/
  theorem spec_9 (nums nums' : Slice I64)
      (hlenn : sliceLen nums = sliceLen nums')
      (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
      (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000)
      (hval' : ∀ i, i < sliceLen nums' → 1 ≤ elemAt nums' i ∧ elemAt nums' i ≤ 1000000000)
      (hshift : ∃ c : Int, ∀ i, i < sliceLen nums → elemAt nums' i = elemAt nums i + c) :
      ∀ r r', Aegis.CountBadPairs.count_bad_pairs nums = ok r →
        Aegis.CountBadPairs.count_bad_pairs nums' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice I64)
        (hlenn : sliceLen nums = sliceLen nums')
        (hlen1 : 1 ≤ sliceLen nums) (hlen2 : sliceLen nums ≤ 100000)
        (hval : ∀ i, i < sliceLen nums → 1 ≤ elemAt nums i ∧ elemAt nums i ≤ 1000000000)
        (hval' : ∀ i, i < sliceLen nums' → 1 ≤ elemAt nums' i ∧ elemAt nums' i ≤ 1000000000)
        (hshift : ∃ c : Int, ∀ i, i < sliceLen nums → elemAt nums' i = elemAt nums i + c), ∀ r r', Aegis.CountBadPairs.count_bad_pairs nums = ok r →
          Aegis.CountBadPairs.count_bad_pairs nums' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.CountBadPairs
