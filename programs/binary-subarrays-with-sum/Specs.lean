import Aegis.NumSubarraysWithSum.Code.Funs

/-!
# Specifications of `Aegis.NumSubarraysWithSum.num_subarrays_with_sum`

LeetCode problem `binary-subarrays-with-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumSubarraysWithSum

  abbrev I64 := Aeneas.Std.I64

  abbrev I64Slice := Aeneas.Std.Slice Aeneas.Std.I64

  def entry (nums : I64Slice) (i : Nat) : Int :=
    ((nums.val[i]?).map (fun x => x.val)).getD 0

  def IsBinary (nums : I64Slice) : Prop :=
    ∀ (i : Nat) (v : I64), nums.val[i]? = some v → v.val = 0 ∨ v.val = 1

  def subarraySum (nums : I64Slice) (l u : Nat) : Int :=
    ∑ i ∈ Finset.range (u + 1 - l), entry nums (l + i)

  def totalSum (nums : I64Slice) : Int :=
    ∑ i ∈ Finset.range nums.val.length, entry nums i

  def countSubarrays (nums : I64Slice) (goal : Int) : Nat :=
    (((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
      (fun p : Nat × Nat => p.1 ≤ p.2 ∧ subarraySum nums p.1 p.2 = goal)).card

  def IsMaximalZeroBlock (nums : I64Slice) (a L : Nat) : Prop :=
    0 < L ∧
      a + L ≤ nums.val.length ∧
      (∀ i, a ≤ i → i < a + L → entry nums i = 0) ∧
      (a = 0 ∨ (0 < a ∧ entry nums (a - 1) = 1)) ∧
      (a + L = nums.val.length ∨ entry nums (a + L) = 1)

  noncomputable def zeroBlockScore (nums : I64Slice) : Nat := by
    classical
    exact ∑ a ∈ Finset.range (nums.val.length + 1),
      ∑ L ∈ Finset.range (nums.val.length + 1),
        if IsMaximalZeroBlock nums a L then L * (L + 1) / 2 else 0

  def onePositions (nums : I64Slice) : List Nat :=
    (List.range nums.val.length).filter (fun i => entry nums i = 1)

  def numOnes (nums : I64Slice) : Nat :=
    (onePositions nums).length

  def numZeros (nums : I64Slice) : Nat :=
    ((List.range nums.val.length).filter (fun i => entry nums i = 0)).length

  def goalIndex (goal : I64) : Nat :=
    goal.val.toNat

  def extOnePosition (nums : I64Slice) (i : Nat) : Int :=
    if i = 0 then -1
    else
      match (onePositions nums)[i - 1]? with
      | some p => (p : Int)
      | none => (nums.val.length : Int)

  def IsFirstOne (nums : I64Slice) (p : Nat) : Prop :=
    entry nums p = 1 ∧ ∀ j, j < p → entry nums j = 0

  def IsLastOne (nums : I64Slice) (q : Nat) : Prop :=
    entry nums q = 1 ∧ ∀ j, q < j → j < nums.val.length → entry nums j = 0

  def reverse (nums : I64Slice) : I64Slice where
    leng := nums.val.reverse.length
    list := Aeneas.Data.ListN.ListN.fromList nums.val.reverse
    bound := by
      simp only [List.length_reverse]
      exact Aeneas.Data.ListN.ListN_length nums.list ▸ nums.bound

  /-- The function returns a result r (so it does not fail), and r is the number of pairs of integers (l, u) such that 0 <= l <= u < len(nums) and the mathematical sum nums[l] + nums[l+1] + ... + nums[u] equals goal. Equivalently, r is the number of non-empty contiguous subarrays of nums whose sum is goal.
    Preconditions: 1 <= len(nums) <= 30000, and for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, and 0 <= goal <= len(nums). -/
  theorem spec_1 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)) :
      ∃ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r ∧
          r.val = (countSubarrays nums goal.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)), ∃ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r ∧
            r.val = (countSubarrays nums goal.val : Int)) := by
    sorry

  /-- The function returns a result value; it does not fail by panic, out-of-bounds indexing, or arithmetic overflow.
    Preconditions: 1 <= len(nums) <= 30000, and for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, and 0 <= goal <= len(nums). -/
  theorem spec_2 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)) :
      ∃ r : I64, Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)), ∃ r : I64, Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(nums) * (len(nums) + 1) / 2, where the product and division are mathematical integers.
    Preconditions: 1 <= len(nums) <= 30000, and for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, and 0 <= goal <= len(nums). -/
  theorem spec_3 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)) :
      ∀ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
          0 ≤ r.val ∧ r.val ≤ ((nums.val.length * (nums.val.length + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)), ∀ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
            0 ≤ r.val ∧ r.val ≤ ((nums.val.length * (nums.val.length + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r equals the sum, over all maximal contiguous zero blocks of nums, of L * (L + 1) / 2, where L is the length of that block. A maximal zero block is a non-empty interval [a,b] such that nums[k] = 0 for all a <= k <= b, and either a = 0 or nums[a-1] = 1, and either b = len(nums)-1 or nums[b+1] = 1. The sum over no blocks is 0.
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, goal = 0, and 0 <= goal <= len(nums). -/
  theorem spec_4 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal : goal.val = 0)
      (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)) :
      ∀ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
          r.val = (zeroBlockScore nums : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal : goal.val = 0)
        (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)), ∀ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
            r.val = (zeroBlockScore nums : Int)) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, 0 <= goal <= len(nums), and goal > the mathematical sum nums[0] + nums[1] + ... + nums[len(nums)-1]. -/
  theorem spec_5 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int))
      (hgt : totalSum nums < goal.val) :
      ∃ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int))
        (hgt : totalSum nums < goal.val), ∃ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r ∧ r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if every entry of nums is 1.
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, and goal = 0. -/
  theorem spec_6 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal : goal.val = 0) :
      ∀ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
          (r.val = 0 ↔ ∀ i, i < nums.val.length → entry nums i = 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal : goal.val = 0), ∀ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
            (r.val = 0 ↔ ∀ i, i < nums.val.length → entry nums i = 1)) := by
    sorry

  /-- Whenever the function returns a result r, let p_1 < p_2 < ... < p_m be the strictly increasing list of all indices i with nums[i] = 1, and set p_0 = -1 and p_{m+1} = len(nums). If m < goal then r = 0; otherwise r = sum_{a=1}^{m-goal+1} (p_a - p_{a-1}) * (p_{a+goal} - p_{a+goal-1}).
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, and 1 <= goal <= len(nums). -/
  theorem spec_7 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal1 : 1 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)) :
      ∀ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
          (numOnes nums < goalIndex goal → r.val = 0) ∧
            (goalIndex goal ≤ numOnes nums →
              r.val = ∑ a ∈ Finset.Icc 1 (numOnes nums + 1 - goalIndex goal),
                (extOnePosition nums a - extOnePosition nums (a - 1)) *
                  (extOnePosition nums (a + goalIndex goal) -
                    extOnePosition nums (a + goalIndex goal - 1))) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal1 : 1 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)), ∀ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
            (numOnes nums < goalIndex goal → r.val = 0) ∧
              (goalIndex goal ≤ numOnes nums →
                r.val = ∑ a ∈ Finset.Icc 1 (numOnes nums + 1 - goalIndex goal),
                  (extOnePosition nums a - extOnePosition nums (a - 1)) *
                    (extOnePosition nums (a + goalIndex goal) -
                      extOnePosition nums (a + goalIndex goal - 1)))) := by
    sorry

  /-- Whenever the function returns a result r, let p be the smallest index with nums[p] = 1 and let q be the largest index with nums[q] = 1. Then r = (p + 1) * (len(nums) - q).
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, the mathematical sum nums[0] + ... + nums[len(nums)-1] is positive, and goal equals that sum. -/
  theorem spec_8 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hpos : 0 < totalSum nums) (hgoal : goal.val = totalSum nums) :
      ∀ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
          ∀ p q : Nat, IsFirstOne nums p → IsLastOne nums q →
            r.val = ((p : Int) + 1) * ((nums.val.length : Int) - (q : Int)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hpos : 0 < totalSum nums) (hgoal : goal.val = totalSum nums), ∀ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
            ∀ p q : Nat, IsFirstOne nums p → IsLastOne nums q →
              r.val = ((p : Int) + 1) * ((nums.val.length : Int) - (q : Int))) := by
    sorry

  /-- For every binary slice nums satisfying the preconditions, let rev be the slice of the same length with rev[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums). Whenever a call on nums returns r and a call on rev returns r_rev, we have r = r_rev.
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, and 0 <= goal <= len(nums). -/
  theorem spec_9 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)) :
      ∀ r rrev : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum (reverse nums) goal = ok rrev →
            r = rrev := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)), ∀ r rrev : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
            Aegis.NumSubarraysWithSum.num_subarrays_with_sum (reverse nums) goal = ok rrev →
              r = rrev) := by
    sorry

  /-- Whenever the function returns a result r, r >= Z, where Z is the number of indices i with 0 <= i < len(nums) and nums[i] = 0.
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, and goal = 0. -/
  theorem spec_10 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal : goal.val = 0) :
      ∀ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
          (numZeros nums : Int) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal : goal.val = 0), ∀ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
            (numZeros nums : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if the number of indices i with nums[i] = 1 is less than goal.
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, and 1 <= goal <= len(nums). -/
  theorem spec_11 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal1 : 1 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)) :
      ∀ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
          (r.val = 0 ↔ numOnes nums < goalIndex goal) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal1 : 1 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)), ∀ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
            (r.val = 0 ↔ numOnes nums < goalIndex goal)) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exist integers l and u with 0 <= l <= u < len(nums) and nums[l] + nums[l+1] + ... + nums[u] = goal.
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, and 0 <= goal <= len(nums). -/
  theorem spec_12 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)) :
      ∀ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
          (0 < r.val ↔
            ∃ l u : Nat, l ≤ u ∧ u < nums.val.length ∧ subarraySum nums l u = goal.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal0 : 0 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)), ∀ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
            (0 < r.val ↔
              ∃ l u : Nat, l ≤ u ∧ u < nums.val.length ∧ subarraySum nums l u = goal.val)) := by
    sorry

  /-- Whenever the calls on nums with each goal g in 0..len(nums) all return results r_g, we have sum_{g=0}^{len(nums)} r_g = len(nums) * (len(nums) + 1) / 2, interpreted as mathematical integers; indeed every non-empty contiguous subarray has exactly one sum, which lies in 0..len(nums).
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_13 (nums : I64Slice)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (r : Nat → Int)
      (hret : ∀ (g : Nat) (gi : I64), gi.val = (g : Int) → g ≤ nums.val.length →
        ∃ ri : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums gi = ok ri ∧ ri.val = r g) :
      (∑ g ∈ Finset.range (nums.val.length + 1), r g) =
        ((nums.val.length * (nums.val.length + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : I64Slice)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (r : Nat → Int)
        (hret : ∀ (g : Nat) (gi : I64), gi.val = (g : Int) → g ≤ nums.val.length →
          ∃ ri : I64,
            Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums gi = ok ri ∧ ri.val = r g), (∑ g ∈ Finset.range (nums.val.length + 1), r g) =
          ((nums.val.length * (nums.val.length + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, let m be the number of indices i with nums[i] = 1; then r = 0 if m < goal, and r >= m - goal + 1 if m >= goal.
    Preconditions: 1 <= len(nums) <= 30000, for every integer i with 0 <= i < len(nums), nums[i] is either 0 or 1, 1 <= goal <= len(nums). -/
  theorem spec_14 (nums : I64Slice) (goal : I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hbin : IsBinary nums)
      (hgoal1 : 1 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)) :
      ∀ r : I64,
        Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
          (numOnes nums < goalIndex goal → r.val = 0) ∧
            (goalIndex goal ≤ numOnes nums →
              (numOnes nums : Int) - goal.val + 1 ≤ r.val) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : I64Slice) (goal : I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hbin : IsBinary nums)
        (hgoal1 : 1 ≤ goal.val) (hgoaln : goal.val ≤ (nums.val.length : Int)), ∀ r : I64,
          Aegis.NumSubarraysWithSum.num_subarrays_with_sum nums goal = ok r →
            (numOnes nums < goalIndex goal → r.val = 0) ∧
              (goalIndex goal ≤ numOnes nums →
                (numOnes nums : Int) - goal.val + 1 ≤ r.val)) := by
    sorry

  end AegisSpec.NumSubarraysWithSum
