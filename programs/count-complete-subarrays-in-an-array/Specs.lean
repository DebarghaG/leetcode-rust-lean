import Aegis.CountCompleteSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountCompleteSubarrays.count_complete_subarrays`

LeetCode problem `count-complete-subarrays-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountCompleteSubarrays

  def elems (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def elem (nums : Slice Std.I64) (i : Nat) : Int := (elems nums).getD i 0

  def winVals (nums : Slice Std.I64) (i j : Nat) : List Int :=
    ((elems nums).drop i).take (j + 1 - i)

  def winSet (nums : Slice Std.I64) (i j : Nat) : Finset Int := (winVals nums i j).toFinset

  def valSet (nums : Slice Std.I64) : Finset Int := (elems nums).toFinset

  def Complete (nums : Slice Std.I64) (i j : Nat) : Prop := winSet nums i j = valSet nums

  def HasAllVals (nums : Slice Std.I64) (i j : Nat) : Prop :=
    ∀ v ∈ valSet nums, ∃ k, i ≤ k ∧ k ≤ j ∧ elem nums k = v

  noncomputable def completeCount (nums : Slice Std.I64) : Nat := by
    classical
    exact (((Finset.range (elems nums).length).product
      (Finset.range (elems nums).length)).filter
        (fun x => x.1 ≤ x.2 ∧ Complete nums x.1 x.2)).card

  /-- The function returns a result r, and r equals the number of pairs (i, j) of integers such that 0 <= i <= j < n and the contiguous non-empty subarray nums[i..j] (that is, nums[i], nums[i+1], ..., nums[j]) has exactly as many distinct values as the whole array nums. Equivalently, letting D = |{nums[k] : 0 <= k < n}|, r = |{(i, j) : 0 <= i <= j < n and |{nums[k] : i <= k <= j}| = D}|.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 2000. -/
  theorem spec_1 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000) :
      ∃ r : Std.I64,
        Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
          r.val = (completeCount nums : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000), ∃ r : Std.I64,
          Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
            r.val = (completeCount nums : Int)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 2000. -/
  theorem spec_2 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000) :
      ∃ r : Std.I64, Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000), ∃ r : Std.I64, Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r) := by
    sorry

  /-- The returned r satisfies r >= 1. Moreover, the whole array nums[0..n-1] is complete, because its set of distinct values is exactly the set of distinct values of nums.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 2000. -/
  theorem spec_3 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000) :
      ∃ r : Std.I64,
        Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
          1 ≤ r.val ∧
            Complete nums 0 (n - 1) ∧
              (winSet nums 0 (n - 1)).card = (valSet nums).card := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000), ∃ r : Std.I64,
          Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
            1 ≤ r.val ∧
              Complete nums 0 (n - 1) ∧
                (winSet nums 0 (n - 1)).card = (valSet nums).card) := by
    sorry

  /-- The function returns r = n * (n + 1) / 2. Equivalently, every contiguous non-empty subarray of nums is complete.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums[i] <= 2000, and the whole array has exactly one distinct value (D = |{nums[k] : 0 <= k < n}| = 1). -/
  theorem spec_4 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
      (hD : (valSet nums).card = 1) :
      ∃ r : Std.I64,
        Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
          r.val = ((n * (n + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
        (hD : (valSet nums).card = 1), ∃ r : Std.I64,
          Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
            r.val = ((n * (n + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- The function returns r = 1; the only complete subarray is the whole array nums[0..n-1].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, for every i with 0 <= i < n, 1 <= nums[i] <= 2000, and the entries of nums are pairwise distinct (D = |{nums[k] : 0 <= k < n}| = n). -/
  theorem spec_5 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
      (hD : (valSet nums).card = n) :
      ∃ r : Std.I64,
        Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
        (hD : (valSet nums).card = n), ∃ r : Std.I64,
          Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧ r.val = 1) := by
    sorry

  /-- Let D = |{nums[k] : 0 <= k < n}|. The returned r satisfies r <= (n - D + 1) * (n - D + 2) / 2, which is the number of contiguous non-empty subarrays of nums whose length is at least D.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 2000. -/
  theorem spec_6 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000) :
      ∃ r : Std.I64,
        Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
          r.val ≤ (((n - (valSet nums).card + 1) * (n - (valSet nums).card + 2)) / 2 : Nat) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000), ∃ r : Std.I64,
          Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
            r.val ≤ (((n - (valSet nums).card + 1) * (n - (valSet nums).card + 2)) / 2 : Nat)) := by
    sorry

  /-- For every 0 <= i <= j < n, the subarray nums[i..j] is complete with respect to nums if and only if the subarray nums'[i..j] is complete with respect to nums'. Consequently, the returned value r for nums equals the value returned by count_complete_subarrays on nums'.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 2000. Let nums' be any array of length n satisfying 1 <= nums'[i] <= 2000 for all i and having the same equality pattern as nums: for all 0 <= i < n and 0 <= j < n, nums[i] = nums[j] if and only if nums'[i] = nums'[j]. -/
  theorem spec_7 (nums nums' : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn' : n = nums'.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
      (hvals' : ∀ i, i < n → 1 ≤ elem nums' i ∧ elem nums' i ≤ 2000)
      (hpat : ∀ i j : Nat, i < n → j < n → (elem nums i = elem nums j ↔ elem nums' i = elem nums' j)) :
      (∀ i j : Nat, i ≤ j → j < n → (Complete nums i j ↔ Complete nums' i j)) ∧
        completeCount nums' = completeCount nums ∧
          (∀ r r' : Std.I64,
            Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r →
              Aegis.CountCompleteSubarrays.count_complete_subarrays nums' = ok r' →
                r.val = r'.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn' : n = nums'.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
        (hvals' : ∀ i, i < n → 1 ≤ elem nums' i ∧ elem nums' i ≤ 2000)
        (hpat : ∀ i j : Nat, i < n → j < n → (elem nums i = elem nums j ↔ elem nums' i = elem nums' j)), (∀ i j : Nat, i ≤ j → j < n → (Complete nums i j ↔ Complete nums' i j)) ∧
          completeCount nums' = completeCount nums ∧
            (∀ r r' : Std.I64,
              Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r →
                Aegis.CountCompleteSubarrays.count_complete_subarrays nums' = ok r' →
                  r.val = r'.val)) := by
    sorry

  /-- Let rev be the array defined by rev[k] = nums[n - 1 - k] for 0 <= k < n. For every 0 <= i <= j < n, nums[i..j] is complete in nums if and only if rev[n - 1 - j .. n - 1 - i] is complete in rev. Consequently, the returned r for nums equals the number of complete subarrays of rev.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 2000. -/
  theorem spec_8 (nums rev : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn_rev : rev.val.length = n)
      (hrev : rev.val = nums.val.reverse)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
      (hvals_rev : ∀ i, i < n → 1 ≤ elem rev i ∧ elem rev i ≤ 2000) :
      (∀ i j : Nat, i ≤ j → j < n →
          (Complete nums i j ↔ Complete rev (n - 1 - j) (n - 1 - i))) ∧
        completeCount rev = completeCount nums ∧
          (∀ r : Std.I64,
            Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r →
              r.val = (completeCount rev : Int)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums rev : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn_rev : rev.val.length = n)
        (hrev : rev.val = nums.val.reverse)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
        (hvals_rev : ∀ i, i < n → 1 ≤ elem rev i ∧ elem rev i ≤ 2000), (∀ i j : Nat, i ≤ j → j < n →
            (Complete nums i j ↔ Complete rev (n - 1 - j) (n - 1 - i))) ∧
          completeCount rev = completeCount nums ∧
            (∀ r : Std.I64,
              Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r →
                r.val = (completeCount rev : Int))) := by
    sorry

  /-- The function returns r = p * q.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 2000. Suppose there exist positive integers p and q with p + q = n and two distinct values a and b such that nums[i] = a for 0 <= i < p and nums[i] = b for p <= i < n. -/
  theorem spec_9 (nums : Slice Std.I64) (n p q : Nat) (a b : Int)
      (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
      (hp : 0 < p) (hq : 0 < q) (hpq : p + q = n) (hab : a ≠ b)
      (hleft : ∀ i, i < p → elem nums i = a)
      (hright : ∀ i, p ≤ i → i < n → elem nums i = b) :
      ∃ r : Std.I64,
        Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
          r.val = ((p * q : Nat) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n p q : Nat) (a b : Int)
        (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
        (hp : 0 < p) (hq : 0 < q) (hpq : p + q = n) (hab : a ≠ b)
        (hleft : ∀ i, i < p → elem nums i = a)
        (hright : ∀ i, p ≤ i → i < n → elem nums i = b), ∃ r : Std.I64,
          Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
            r.val = ((p * q : Nat) : Int)) := by
    sorry

  /-- The function returns r = n * (n - 1) / 2. Equivalently, the complete subarrays are exactly the contiguous subarrays of length at least 2.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 2000. Suppose the whole array has exactly two distinct values (D = |{nums[k] : 0 <= k < n}| = 2) and no two adjacent entries are equal: for every i with 0 <= i < n - 1, nums[i] != nums[i + 1]. -/
  theorem spec_10 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
      (hD : (valSet nums).card = 2)
      (hadj : ∀ i, i + 1 < n → elem nums i ≠ elem nums (i + 1)) :
      ∃ r : Std.I64,
        Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
          r.val = ((n * (n - 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hvals : ∀ i, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 2000)
        (hD : (valSet nums).card = 2)
        (hadj : ∀ i, i + 1 < n → elem nums i ≠ elem nums (i + 1)), ∃ r : Std.I64,
          Aegis.CountCompleteSubarrays.count_complete_subarrays nums = ok r ∧
            r.val = ((n * (n - 1) / 2 : Nat) : Int)) := by
    sorry

  end AegisSpec.CountCompleteSubarrays
