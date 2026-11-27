import Aegis.LongestAlternatingSubarray.Code.Funs

/-!
# Specifications of `Aegis.LongestAlternatingSubarray.longest_alternating_subarray`

LeetCode problem `longest-even-odd-subarray-with-threshold`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LongestAlternatingSubarray

  namespace AegisSpec.LongestAlternatingSubarray

  def nth (nums : Slice Std.I64) (i : Nat) : Int :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def EvenAt (nums : Slice Std.I64) (l : Nat) : Prop :=
    nth nums l % 2 = 0

  def AlternatingFrom (nums : Slice Std.I64) (l e : Nat) : Prop :=
    ∀ i : Nat, l ≤ i → i < e → nth nums i % 2 ≠ nth nums (i + 1) % 2

  def AllAtMost (nums : Slice Std.I64) (threshold : Int) (l e : Nat) : Prop :=
    ∀ i : Nat, l ≤ i → i ≤ e → nth nums i ≤ threshold

  def AllLeLens (nums : Slice Std.I64) (threshold : Int) : Set Nat :=
    {n | n = 0 ∨ ∃ l e, l ≤ e ∧ e < nums.val.length ∧ AllAtMost nums threshold l e ∧ n = e - l + 1}

  noncomputable def maxAllLeLen (nums : Slice Std.I64) (threshold : Int) : Nat :=
    sSup (AllLeLens nums threshold)

  def AlternatingLens (nums : Slice Std.I64) : Set Nat :=
    {n | n = 0 ∨ ∃ l e, l ≤ e ∧ e < nums.val.length ∧ EvenAt nums l ∧ AlternatingFrom nums l e ∧
      n = e - l + 1}

  noncomputable def maxAlternatingLen (nums : Slice Std.I64) : Nat :=
    sSup (AlternatingLens nums)

  /-- The function returns a result r, and r is the maximum of the set {0} union { e - l + 1 | there exist integers l and e such that 0 <= l <= e < len(nums), nums[l] % 2 == 0, for every i with l <= i < e we have nums[i] % 2 != nums[i+1] % 2, and for every i with l <= i <= e we have nums[i] <= threshold }. Equivalently, if at least one such valid subarray exists then r is the length of a longest one, and if none exists then r = 0.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, and 1 <= threshold <= 100. -/
  theorem spec_1 (nums : Slice Std.I64) (threshold : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100) :
      ∃ r : Std.I64,
        longest_alternating_subarray nums threshold = ok r ∧
          0 ≤ r.val ∧
          (∀ l e : Nat, l ≤ e → e < nums.val.length → EvenAt nums l → AlternatingFrom nums l e →
            AllAtMost nums threshold.val l e → ((e : Int) - (l : Int) + 1) ≤ r.val) ∧
          (r.val = 0 ∨
            ∃ l e : Nat, l ≤ e ∧ e < nums.val.length ∧ EvenAt nums l ∧ AlternatingFrom nums l e ∧
              AllAtMost nums threshold.val l e ∧ r.val = (e : Int) - (l : Int) + 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100), ∃ r : Std.I64,
          longest_alternating_subarray nums threshold = ok r ∧
            0 ≤ r.val ∧
            (∀ l e : Nat, l ≤ e → e < nums.val.length → EvenAt nums l → AlternatingFrom nums l e →
              AllAtMost nums threshold.val l e → ((e : Int) - (l : Int) + 1) ≤ r.val) ∧
            (r.val = 0 ∨
              ∃ l e : Nat, l ≤ e ∧ e < nums.val.length ∧ EvenAt nums l ∧ AlternatingFrom nums l e ∧
                AllAtMost nums threshold.val l e ∧ r.val = (e : Int) - (l : Int) + 1)) := by
    sorry

  /-- The function returns a result r; it does not fail for any input satisfying the preconditions.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, and 1 <= threshold <= 100. -/
  theorem spec_2 (nums : Slice Std.I64) (threshold : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100) :
      ∃ r : Std.I64, longest_alternating_subarray nums threshold = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100), ∃ r : Std.I64, longest_alternating_subarray nums threshold = ok r) := by
    sorry

  /-- Whenever the function returns a result r, we have 0 <= r <= len(nums).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, and 1 <= threshold <= 100. -/
  theorem spec_3 (nums : Slice Std.I64) (threshold : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100) :
      ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
        0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100), ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
          0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there is no index i with 0 <= i < len(nums) such that nums[i] % 2 == 0 and nums[i] <= threshold.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, and 1 <= threshold <= 100. -/
  theorem spec_4 (nums : Slice Std.I64) (threshold : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100) :
      ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
        (r.val = 0 ↔ ¬ ∃ i : Nat, i < nums.val.length ∧ EvenAt nums i ∧ nth nums i ≤ threshold.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100), ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
          (r.val = 0 ↔ ¬ ∃ i : Nat, i < nums.val.length ∧ EvenAt nums i ∧ nth nums i ≤ threshold.val)) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exists an integer l such that 0 <= l, l + r <= len(nums), nums[l] % 2 == 0, for every k with 0 <= k < r - 1 we have nums[l+k] % 2 != nums[l+k+1] % 2, and for every k with 0 <= k < r we have nums[l+k] <= threshold.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, and 1 <= threshold <= 100. -/
  theorem spec_5 (nums : Slice Std.I64) (threshold : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100) :
      ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r → 0 < r.val →
        ∃ l : Nat,
          l + r.val.toNat ≤ nums.val.length ∧
            EvenAt nums l ∧
            (∀ k : Nat, k < r.val.toNat - 1 → nth nums (l + k) % 2 ≠ nth nums (l + k + 1) % 2) ∧
            (∀ k : Nat, k < r.val.toNat → nth nums (l + k) ≤ threshold.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100), ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r → 0 < r.val →
          ∃ l : Nat,
            l + r.val.toNat ≤ nums.val.length ∧
              EvenAt nums l ∧
              (∀ k : Nat, k < r.val.toNat - 1 → nth nums (l + k) % 2 ≠ nth nums (l + k + 1) % 2) ∧
              (∀ k : Nat, k < r.val.toNat → nth nums (l + k) ≤ threshold.val)) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of integers l and e with 0 <= l <= e < len(nums), if nums[l] % 2 == 0, for every i with l <= i < e we have nums[i] % 2 != nums[i+1] % 2, and for every i with l <= i <= e we have nums[i] <= threshold, then e - l + 1 <= r.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, and 1 <= threshold <= 100. -/
  theorem spec_6 (nums : Slice Std.I64) (threshold : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100) :
      ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
        ∀ l e : Nat, l ≤ e → e < nums.val.length → EvenAt nums l → AlternatingFrom nums l e →
          AllAtMost nums threshold.val l e → ((e : Int) - (l : Int) + 1) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100), ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
          ∀ l e : Nat, l ≤ e → e < nums.val.length → EvenAt nums l → AlternatingFrom nums l e →
            AllAtMost nums threshold.val l e → ((e : Int) - (l : Int) + 1) ≤ r.val) := by
    sorry

  /-- Let r1 be the result returned by longest_alternating_subarray(nums, t1) and let r2 be the result returned by longest_alternating_subarray(nums, t2). Both calls return results, and r1 <= r2.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, and t1 and t2 are integers with 1 <= t1 <= t2 <= 100. -/
  theorem spec_7 (nums : Slice Std.I64) (t1 t2 : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (h1 : 1 ≤ t1.val) (h12 : t1.val ≤ t2.val) (h2 : t2.val ≤ 100) :
      ∃ r1 r2 : Std.I64,
        longest_alternating_subarray nums t1 = ok r1 ∧
          longest_alternating_subarray nums t2 = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (t1 t2 : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (h1 : 1 ≤ t1.val) (h12 : t1.val ≤ t2.val) (h2 : t2.val ≤ 100), ∃ r1 r2 : Std.I64,
          longest_alternating_subarray nums t1 = ok r1 ∧
            longest_alternating_subarray nums t2 = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  /-- Suppose that for every i with 0 <= i < len(nums), nums[i] <= threshold if and only if nums2[i] <= threshold, and whenever nums[i] <= threshold we have nums[i] % 2 == nums2[i] % 2. Then the result returned by longest_alternating_subarray(nums, threshold) equals the result returned by longest_alternating_subarray(nums2, threshold).
    Preconditions: nums and nums2 are slices of 64-bit integers with equal length, 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100 and 1 <= nums2[i] <= 100, and 1 <= threshold <= 100. -/
  theorem spec_8 (nums nums2 : Slice Std.I64) (threshold : Std.I64)
      (hlen : nums.val.length = nums2.val.length)
      (hlen1 : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hval2 : ∀ i : Nat, i < nums2.val.length → 1 ≤ nth nums2 i ∧ nth nums2 i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100)
      (hsame : ∀ i : Nat, i < nums.val.length →
        (nth nums i ≤ threshold.val ↔ nth nums2 i ≤ threshold.val))
      (hpar : ∀ i : Nat, i < nums.val.length → nth nums i ≤ threshold.val →
        nth nums i % 2 = nth nums2 i % 2) :
      ∃ r : Std.I64,
        longest_alternating_subarray nums threshold = ok r ∧
          longest_alternating_subarray nums2 threshold = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (threshold : Std.I64)
        (hlen : nums.val.length = nums2.val.length)
        (hlen1 : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hval2 : ∀ i : Nat, i < nums2.val.length → 1 ≤ nth nums2 i ∧ nth nums2 i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100)
        (hsame : ∀ i : Nat, i < nums.val.length →
          (nth nums i ≤ threshold.val ↔ nth nums2 i ≤ threshold.val))
        (hpar : ∀ i : Nat, i < nums.val.length → nth nums i ≤ threshold.val →
          nth nums i % 2 = nth nums2 i % 2), ∃ r : Std.I64,
          longest_alternating_subarray nums threshold = ok r ∧
            longest_alternating_subarray nums2 threshold = ok r) := by
    sorry

  /-- The function returns result len(nums) if nums[0] % 2 == 0, and returns result len(nums) - 1 if nums[0] % 2 != 0.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, 1 <= threshold <= 100, for every i with 0 <= i < len(nums) we have nums[i] <= threshold, and for every i with 0 <= i < len(nums)-1 we have nums[i] % 2 != nums[i+1] % 2. -/
  theorem spec_9 (nums : Slice Std.I64) (threshold : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100)
      (hle : ∀ i : Nat, i < nums.val.length → nth nums i ≤ threshold.val)
      (halt : ∀ i : Nat, i < nums.val.length - 1 → nth nums i % 2 ≠ nth nums (i + 1) % 2) :
      ∃ r : Std.I64,
        longest_alternating_subarray nums threshold = ok r ∧
          (EvenAt nums 0 → r.val = (nums.val.length : Int)) ∧
          (¬ EvenAt nums 0 → r.val = (nums.val.length : Int) - 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100)
        (hle : ∀ i : Nat, i < nums.val.length → nth nums i ≤ threshold.val)
        (halt : ∀ i : Nat, i < nums.val.length - 1 → nth nums i % 2 ≠ nth nums (i + 1) % 2), ∃ r : Std.I64,
          longest_alternating_subarray nums threshold = ok r ∧
            (EvenAt nums 0 → r.val = (nums.val.length : Int)) ∧
            (¬ EvenAt nums 0 → r.val = (nums.val.length : Int) - 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) if and only if nums[0] % 2 == 0, for every i with 0 <= i < len(nums) we have nums[i] <= threshold, and for every i with 0 <= i < len(nums)-1 we have nums[i] % 2 != nums[i+1] % 2.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, and 1 <= threshold <= 100. -/
  theorem spec_10 (nums : Slice Std.I64) (threshold : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100) :
      ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
        (r.val = (nums.val.length : Int) ↔
          EvenAt nums 0 ∧ AllAtMost nums threshold.val 0 (nums.val.length - 1) ∧
            AlternatingFrom nums 0 (nums.val.length - 1)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100), ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
          (r.val = (nums.val.length : Int) ↔
            EvenAt nums 0 ∧ AllAtMost nums threshold.val 0 (nums.val.length - 1) ∧
              AlternatingFrom nums 0 (nums.val.length - 1))) := by
    sorry

  /-- Let r1 be the result returned by longest_alternating_subarray(nums, threshold) and let r2 be the result returned by longest_alternating_subarray(nums2, threshold). Both calls return results, and r1 <= r2.
    Preconditions: nums and nums2 are slices of 64-bit integers with 1 <= len(nums) <= len(nums2) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, for every i with 0 <= i < len(nums2) we have 1 <= nums2[i] <= 100, for every i with 0 <= i < len(nums) we have nums2[i] = nums[i], and 1 <= threshold <= 100. -/
  theorem spec_11 (nums nums2 : Slice Std.I64) (threshold : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ nums2.val.length)
      (hlen2 : nums2.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hval2 : ∀ i : Nat, i < nums2.val.length → 1 ≤ nth nums2 i ∧ nth nums2 i ≤ 100)
      (hpref : ∀ i : Nat, i < nums.val.length → nth nums2 i = nth nums i)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100) :
      ∃ r1 r2 : Std.I64,
        longest_alternating_subarray nums threshold = ok r1 ∧
          longest_alternating_subarray nums2 threshold = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (threshold : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen : nums.val.length ≤ nums2.val.length)
        (hlen2 : nums2.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hval2 : ∀ i : Nat, i < nums2.val.length → 1 ≤ nth nums2 i ∧ nth nums2 i ≤ 100)
        (hpref : ∀ i : Nat, i < nums.val.length → nth nums2 i = nth nums i)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100), ∃ r1 r2 : Std.I64,
          longest_alternating_subarray nums threshold = ok r1 ∧
            longest_alternating_subarray nums2 threshold = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  /-- Let B be the maximum of the set {0} union { e - l + 1 | there exist integers l and e such that 0 <= l <= e < len(nums) and for every i with l <= i <= e we have nums[i] <= threshold }. Whenever the function returns a result r, r <= B.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, and 1 <= threshold <= 100. -/
  theorem spec_12 (nums : Slice Std.I64) (threshold : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100) :
      ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
        r.val ≤ (maxAllLeLen nums threshold.val : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100), ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
          r.val ≤ (maxAllLeLen nums threshold.val : Int)) := by
    sorry

  /-- Let A be the maximum of the set {0} union { e - l + 1 | there exist integers l and e such that 0 <= l <= e < len(nums), nums[l] % 2 == 0, and for every i with l <= i < e we have nums[i] % 2 != nums[i+1] % 2 }. Whenever the function returns a result r, r <= A.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100, for every i with 0 <= i < len(nums) we have 1 <= nums[i] <= 100, and 1 <= threshold <= 100. -/
  theorem spec_13 (nums : Slice Std.I64) (threshold : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
      (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
      (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100) :
      ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
        r.val ≤ (maxAlternatingLen nums : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 100)
        (hval : ∀ i : Nat, i < nums.val.length → 1 ≤ nth nums i ∧ nth nums i ≤ 100)
        (hth : 1 ≤ threshold.val ∧ threshold.val ≤ 100), ∀ r : Std.I64, longest_alternating_subarray nums threshold = ok r →
          r.val ≤ (maxAlternatingLen nums : Int)) := by
    sorry

  end AegisSpec.LongestAlternatingSubarray
