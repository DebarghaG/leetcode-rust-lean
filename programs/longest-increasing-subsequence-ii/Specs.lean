import Aegis.LengthOfLis.Code.Funs

/-!
# Specifications of `Aegis.LengthOfLis.length_of_lis`

LeetCode problem `longest-increasing-subsequence-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LengthOfLis

  def valueAt (nums : List Std.I64) (i : Nat) : Option ℤ := (nums[i]?).map (fun x => x.val)

  def Adjacent {α : Type} (R : α → α → Prop) : List α → Prop
    | [] => True
    | [_] => True
    | a :: b :: t => R a b ∧ Adjacent R (b :: t)

  def selected (nums : List Std.I64) (idxs : List Nat) : List ℤ :=
    idxs.map (fun i => (valueAt nums i).getD 0)

  def IsValidSubseq (nums : List Std.I64) (k : ℤ) (idxs : List Nat) : Prop :=
    idxs.Pairwise (· < ·) ∧
      (∀ i ∈ idxs, i < nums.length) ∧
      Adjacent (fun a b : ℤ => a < b ∧ b - a ≤ k) (selected nums idxs)

  def IsIncreasingSubseq (nums : List Std.I64) (idxs : List Nat) : Prop :=
    idxs.Pairwise (· < ·) ∧
      (∀ i ∈ idxs, i < nums.length) ∧
      Adjacent (fun a b : ℤ => a < b) (selected nums idxs)

  def distinctCount (nums : Slice Std.I64) : Nat :=
    (nums.val.map (fun x => x.val)).dedup.length

  def maxValue (nums : List Std.I64) : ℤ :=
    match nums.map (fun x => x.val) with
    | [] => 0
    | x :: xs => xs.foldr max x

  def minValue (nums : List Std.I64) : ℤ :=
    match nums.map (fun x => x.val) with
    | [] => 0
    | x :: xs => xs.foldr min x

  def rangeValues (nums : List Std.I64) (l u : Nat) : List ℤ :=
    ((nums.drop l).take (u + 1 - l)).map (fun x => x.val)

  def IsShiftOf (nums nums' : Slice Std.I64) (c : ℤ) : Prop :=
    nums'.val.length = nums.val.length ∧
      ∀ (i : Nat) (hi : i < nums.val.length),
        valueAt nums'.val i = some ((nums.val[i]'hi).val + c)

  /-- The function returns a result r (it does not fail). Call an index sequence 0 <= i_0 < ... < i_{m-1} < len(nums) a valid subsequence of nums for k if for every j with 0 <= j < m-1, nums[i_j] < nums[i_{j+1}] and nums[i_{j+1}] - nums[i_j] <= k. Then r is the maximum m for which a valid subsequence of nums of length m exists. Equivalently, there exists a valid subsequence of length r, and every valid subsequence has length at most r.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : Std.I64,
        Aegis.LengthOfLis.length_of_lis nums k = ok r ∧
          (∃ idxs : List Nat, IsValidSubseq nums.val k.val idxs ∧ (idxs.length : ℤ) = r.val) ∧
          (∀ idxs : List Nat, IsValidSubseq nums.val k.val idxs →
            (idxs.length : ℤ) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : Std.I64,
          Aegis.LengthOfLis.length_of_lis nums k = ok r ∧
            (∃ idxs : List Nat, IsValidSubseq nums.val k.val idxs ∧ (idxs.length : ℤ) = r.val) ∧
            (∀ idxs : List Nat, IsValidSubseq nums.val k.val idxs →
              (idxs.length : ℤ) ≤ r.val)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular, it does not overflow, go out of bounds, or panic.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= len(nums).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
        1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
          1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= the number of distinct values in nums, that is, the cardinality of the set {nums[i] | 0 <= i < len(nums)}.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
        r.val ≤ (distinctCount nums : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
          r.val ≤ (distinctCount nums : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a valid subsequence of nums for k of length r, where a valid subsequence is an index sequence 0 <= i_0 < ... < i_{m-1} < len(nums) such that for every j with 0 <= j < m-1, nums[i_j] < nums[i_{j+1}] and nums[i_{j+1}] - nums[i_j] <= k.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
        ∃ idxs : List Nat, IsValidSubseq nums.val k.val idxs ∧ (idxs.length : ℤ) = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
          ∃ idxs : List Nat, IsValidSubseq nums.val k.val idxs ∧ (idxs.length : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, every valid subsequence of nums for k has length at most r, where a valid subsequence is an index sequence 0 <= i_0 < ... < i_{m-1} < len(nums) such that for every j with 0 <= j < m-1, nums[i_j] < nums[i_{j+1}] and nums[i_{j+1}] - nums[i_j] <= k.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
        ∀ idxs : List Nat, IsValidSubseq nums.val k.val idxs →
          (idxs.length : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
          ∀ idxs : List Nat, IsValidSubseq nums.val k.val idxs →
            (idxs.length : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] and nums[i+1] - nums[i] <= k. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hadj : Adjacent (fun a b : ℤ => a < b ∧ b - a ≤ k.val)
        (nums.val.map (fun x => x.val))) :
      ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
        r.val = (nums.val.length : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hadj : Adjacent (fun a b : ℤ => a < b ∧ b - a ≤ k.val)
          (nums.val.map (fun x => x.val))), ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
          r.val = (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever length_of_lis(nums, k1) returns a result r1 and length_of_lis(nums, k2) returns a result r2, we have r1 <= r2.
    Preconditions: For the same slice nums, 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k1 <= 100000; 1 <= k2 <= 100000; k1 <= k2. -/
  theorem spec_8 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1lo : 1 ≤ k1.val) (hk1hi : k1.val ≤ 100000)
      (hk2lo : 1 ≤ k2.val) (hk2hi : k2.val ≤ 100000)
      (hk : k1.val ≤ k2.val) :
      ∀ r1 r2 : Std.I64,
        Aegis.LengthOfLis.length_of_lis nums k1 = ok r1 →
        Aegis.LengthOfLis.length_of_lis nums k2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1lo : 1 ≤ k1.val) (hk1hi : k1.val ≤ 100000)
        (hk2lo : 1 ≤ k2.val) (hk2hi : k2.val ≤ 100000)
        (hk : k1.val ≤ k2.val), ∀ r1 r2 : Std.I64,
          Aegis.LengthOfLis.length_of_lis nums k1 = ok r1 →
          Aegis.LengthOfLis.length_of_lis nums k2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns a result r, r equals the largest m for which there exist indices 0 <= j_0 < ... < j_{m-1} < len(nums) with nums[j_t] < nums[j_{t+1}] for every t with 0 <= t < m-1 (a longest strictly increasing subsequence ignoring the adjacent-difference condition).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000; k >= max(nums) - min(nums), where max(nums) and min(nums) are the maximum and minimum of all elements of nums. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hbig : maxValue nums.val - minValue nums.val ≤ k.val) :
      ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
        (∃ idxs : List Nat, IsIncreasingSubseq nums.val idxs ∧ (idxs.length : ℤ) = r.val) ∧
          (∀ idxs : List Nat, IsIncreasingSubseq nums.val idxs →
            (idxs.length : ℤ) ≤ r.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hbig : maxValue nums.val - minValue nums.val ≤ k.val), ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
          (∃ idxs : List Nat, IsIncreasingSubseq nums.val idxs ∧ (idxs.length : ℤ) = r.val) ∧
            (∀ idxs : List Nat, IsIncreasingSubseq nums.val idxs →
              (idxs.length : ℤ) ≤ r.val)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000; for every i and j with 0 <= i < j < len(nums) and nums[i] < nums[j], we have nums[j] - nums[i] > k. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hfar : ∀ (i : Nat) (hi : i < nums.val.length) (j : Nat) (hj : j < nums.val.length),
        i < j → (nums.val[i]'hi).val < (nums.val[j]'hj).val →
          k.val < (nums.val[j]'hj).val - (nums.val[i]'hi).val) :
      ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r → r.val = 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hfar : ∀ (i : Nat) (hi : i < nums.val.length) (j : Nat) (hj : j < nums.val.length),
          i < j → (nums.val[i]'hi).val < (nums.val[j]'hj).val →
            k.val < (nums.val[j]'hj).val - (nums.val[i]'hi).val), ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r >= 2 if and only if there exist indices i and j with 0 <= i < j < len(nums), nums[i] < nums[j], and nums[j] - nums[i] <= k.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
        (2 ≤ r.val ↔
          ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
            i < j ∧ (nums.val[i]'hi).val < (nums.val[j]'hj).val ∧
              (nums.val[j]'hj).val - (nums.val[i]'hi).val ≤ k.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
          (2 ≤ r.val ↔
            ∃ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
              i < j ∧ (nums.val[i]'hi).val < (nums.val[j]'hj).val ∧
                (nums.val[j]'hj).val - (nums.val[i]'hi).val ≤ k.val)) := by
    sorry

  /-- Let nums+c be the slice of the same length with (nums+c)[i] = nums[i] + c for every i. Whenever length_of_lis(nums, k) returns a result r and length_of_lis(nums+c, k) returns a result r', we have r = r'.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000; c is an integer such that for every i with 0 <= i < len(nums), 1 <= nums[i] + c <= 100000. -/
  theorem spec_12 (nums nums' : Slice Std.I64) (k : Std.I64) (c : ℤ)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
      (hval' : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val + c ∧ (nums.val[i]'hi).val + c ≤ 100000)
      (hshift : IsShiftOf nums nums' c) :
      ∀ r r' : Std.I64,
        Aegis.LengthOfLis.length_of_lis nums k = ok r →
        Aegis.LengthOfLis.length_of_lis nums' k = ok r' → r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (c : ℤ)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
        (hval' : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val + c ∧ (nums.val[i]'hi).val + c ≤ 100000)
        (hshift : IsShiftOf nums nums' c), ∀ r r' : Std.I64,
          Aegis.LengthOfLis.length_of_lis nums k = ok r →
          Aegis.LengthOfLis.length_of_lis nums' k = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of indices l and u with 0 <= l <= u < len(nums) such that for every i with l <= i < u, nums[i] < nums[i+1] and nums[i+1] - nums[i] <= k, we have r >= u - l + 1.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000. -/
  theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
        ∀ (l u : Nat) (hl : l ≤ u) (hu : u < nums.val.length),
          Adjacent (fun a b : ℤ => a < b ∧ b - a ≤ k.val) (rangeValues nums.val l u) →
            ((u - l + 1 : Nat) : ℤ) ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
          ∀ (l u : Nat) (hl : l ≤ u) (hu : u < nums.val.length),
            Adjacent (fun a b : ℤ => a < b ∧ b - a ≤ k.val) (rangeValues nums.val l u) →
              ((u - l + 1 : Nat) : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r is at most the largest m for which there exist indices 0 <= j_0 < ... < j_{m-1} < len(nums) with nums[j_t] < nums[j_{t+1}] for every t with 0 <= t < m-1 (the ordinary strictly increasing subsequence length without the adjacent-difference condition).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; 1 <= k <= 100000. -/
  theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
        ∀ idxs : List Nat, IsIncreasingSubseq nums.val idxs → r.val ≤ (idxs.length : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∀ r : Std.I64, Aegis.LengthOfLis.length_of_lis nums k = ok r →
          ∀ idxs : List Nat, IsIncreasingSubseq nums.val idxs → r.val ≤ (idxs.length : ℤ)) := by
    sorry

  end AegisSpec.LengthOfLis
