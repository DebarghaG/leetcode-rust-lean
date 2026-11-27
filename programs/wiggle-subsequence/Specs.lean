import Aegis.WiggleMaxLength.Code.Funs

/-!
# Specifications of `Aegis.WiggleMaxLength.wiggle_max_length`

LeetCode problem `wiggle-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.WiggleMaxLength

  open Aegis.WiggleMaxLength

  def ValidInput (nums : Slice I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 1000 ∧
      ∀ i : Fin nums.val.length, 0 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 1000

  def vals (nums : Slice I64) : List ℤ := nums.val.map fun x => x.val

  def IsWiggle : List ℤ → Prop
    | [] => True
    | [_] => True
    | [x, y] => x ≠ y
    | x :: y :: z :: rest => (y - x) * (z - y) < 0 ∧ IsWiggle (y :: z :: rest)

  def HasWiggleSubseq (l : List ℤ) (k : ℕ) : Prop :=
    ∃ idx : List (Fin l.length), idx.length = k ∧ idx.Pairwise (fun i j => i < j) ∧
      IsWiggle (idx.map fun i => l.get i)

  def AllEqual (l : List ℤ) : Prop := ∀ x ∈ l, ∀ y ∈ l, x = y

  def dedupAux (prev : ℤ) : List ℤ → List ℤ
    | [] => []
    | x :: xs => if x = prev then dedupAux prev xs else x :: dedupAux x xs

  def dedup : List ℤ → List ℤ
    | [] => []
    | x :: xs => x :: dedupAux x xs

  def diffs : List ℤ → List ℤ
    | [] => []
    | [_] => []
    | x :: y :: rest => (y - x) :: diffs (y :: rest)

  def countSignFlips : List ℤ → ℕ
    | [] => 0
    | [_] => 0
    | x :: y :: rest => (if x * y < 0 then 1 else 0) + countSignFlips (y :: rest)

  def Nondecreasing : List ℤ → Prop
    | [] => True
    | [_] => True
    | x :: y :: rest => x ≤ y ∧ Nondecreasing (y :: rest)

  def Nonincreasing : List ℤ → Prop
    | [] => True
    | [_] => True
    | x :: y :: rest => y ≤ x ∧ Nonincreasing (y :: rest)

  /-- The function returns a result r, and r equals the maximum length k such that there exist indices 0 <= i_0 < i_1 < ... < i_{k-1} < len(nums) for which the sequence nums[i_0], nums[i_1], ..., nums[i_{k-1}] is a wiggle sequence. A sequence a_0, a_1, ..., a_{k-1} of integers is a wiggle sequence iff either (i) k <= 1, or (ii) k = 2 and a_0 != a_1, or (iii) k >= 3 and for every j with 0 <= j <= k-3, (a_{j+1} - a_j) * (a_{j+2} - a_{j+1}) < 0.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_1 (nums : Slice I64) (h : ValidInput nums) :
      ∃ r : I64, wiggle_max_length nums = ok r ∧
        HasWiggleSubseq (vals nums) r.val.toNat ∧
        ∀ k : ℕ, HasWiggleSubseq (vals nums) k → (k : ℤ) ≤ r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums), ∃ r : I64, wiggle_max_length nums = ok r ∧
          HasWiggleSubseq (vals nums) r.val.toNat ∧
          ∀ k : ℕ, HasWiggleSubseq (vals nums) k → (k : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r, and 1 <= r <= len(nums).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_2 (nums : Slice I64) (h : ValidInput nums) :
      ∃ r : I64, wiggle_max_length nums = ok r ∧ 1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums), ∃ r : I64, wiggle_max_length nums = ok r ∧ 1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- If len(nums) = 1, then the function returns r = 1.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_3 (nums : Slice I64) (h : ValidInput nums) (hlen : nums.val.length = 1) :
      ∃ r : I64, wiggle_max_length nums = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (hlen : nums.val.length = 1), ∃ r : I64, wiggle_max_length nums = ok r ∧ r.val = 1) := by
    sorry

  /-- If the entire array nums is a wiggle sequence (i.e., the sequence nums[0], nums[1], ..., nums[len(nums)-1] is a wiggle sequence, where a wiggle sequence is defined as in spec_1), then the function returns r = len(nums).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_4 (nums : Slice I64) (h : ValidInput nums) (hwig : IsWiggle (vals nums)) :
      ∃ r : I64, wiggle_max_length nums = ok r ∧ r.val = (nums.val.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (hwig : IsWiggle (vals nums)), ∃ r : I64, wiggle_max_length nums = ok r ∧ r.val = (nums.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r, and there exist indices 0 <= i_0 < i_1 < ... < i_{r-1} < len(nums) such that the sequence nums[i_0], ..., nums[i_{r-1}] is a wiggle sequence (defined as in spec_1).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_5 (nums : Slice I64) (h : ValidInput nums) :
      ∃ r : I64, wiggle_max_length nums = ok r ∧ HasWiggleSubseq (vals nums) r.val.toNat := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums), ∃ r : I64, wiggle_max_length nums = ok r ∧ HasWiggleSubseq (vals nums) r.val.toNat) := by
    sorry

  /-- The function returns a result r, and for every k with r < k <= len(nums), there do not exist indices 0 <= i_0 < i_1 < ... < i_{k-1} < len(nums) such that the sequence nums[i_0], ..., nums[i_{k-1}] is a wiggle sequence (defined as in spec_1).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_6 (nums : Slice I64) (h : ValidInput nums) :
      ∃ r : I64, wiggle_max_length nums = ok r ∧
        ∀ k : ℕ, r.val < (k : ℤ) → k ≤ nums.val.length → ¬ HasWiggleSubseq (vals nums) k := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums), ∃ r : I64, wiggle_max_length nums = ok r ∧
          ∀ k : ℕ, r.val < (k : ℤ) → k ≤ nums.val.length → ¬ HasWiggleSubseq (vals nums) k) := by
    sorry

  /-- The function returns a result r (it does not fail) for every nums satisfying the preconditions.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_7 (nums : Slice I64) (h : ValidInput nums) :
      ∃ r : I64, wiggle_max_length nums = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums), ∃ r : I64, wiggle_max_length nums = ok r) := by
    sorry

  /-- The function returns r for nums and r' for nums', and r = r'.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). c is an integer such that 0 <= nums[i] + c <= 1000 for all 0 <= i < len(nums). Let nums' be the array with nums'[i] = nums[i] + c for all 0 <= i < len(nums). -/
  theorem spec_8 (nums nums' : Slice I64) (c : ℤ) (h : ValidInput nums)
      (hc : ∀ i : Fin nums.val.length,
        0 ≤ (nums.val.get i).val + c ∧ (nums.val.get i).val + c ≤ 1000)
      (hshift : vals nums' = (vals nums).map fun y => y + c) :
      ∃ r r' : I64, wiggle_max_length nums = ok r ∧ wiggle_max_length nums' = ok r' ∧ r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice I64) (c : ℤ) (h : ValidInput nums)
        (hc : ∀ i : Fin nums.val.length,
          0 ≤ (nums.val.get i).val + c ∧ (nums.val.get i).val + c ≤ 1000)
        (hshift : vals nums' = (vals nums).map fun y => y + c), ∃ r r' : I64, wiggle_max_length nums = ok r ∧ wiggle_max_length nums' = ok r' ∧ r = r') := by
    sorry

  /-- The function returns r for nums and r' for rev(nums), and r = r'.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). Let rev(nums) be the array with rev(nums)[i] = nums[len(nums)-1-i] for all 0 <= i < len(nums). -/
  theorem spec_9 (nums nums' : Slice I64) (h : ValidInput nums)
      (hrev : vals nums' = (vals nums).reverse) :
      ∃ r r' : I64, wiggle_max_length nums = ok r ∧ wiggle_max_length nums' = ok r' ∧ r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice I64) (h : ValidInput nums)
        (hrev : vals nums' = (vals nums).reverse), ∃ r r' : I64, wiggle_max_length nums = ok r ∧ wiggle_max_length nums' = ok r' ∧ r = r') := by
    sorry

  /-- The function returns r, and r >= 2 if and only if len(nums) >= 2 and there exist indices i, j with 0 <= i < j < len(nums) and nums[i] != nums[j].
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_10 (nums : Slice I64) (h : ValidInput nums) :
      ∃ r : I64, wiggle_max_length nums = ok r ∧
        (2 ≤ r.val ↔
          2 ≤ nums.val.length ∧
            ∃ i j : Fin nums.val.length, i < j ∧ (nums.val.get i).val ≠ (nums.val.get j).val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums), ∃ r : I64, wiggle_max_length nums = ok r ∧
          (2 ≤ r.val ↔
            2 ≤ nums.val.length ∧
              ∃ i j : Fin nums.val.length, i < j ∧ (nums.val.get i).val ≠ (nums.val.get j).val)) := by
    sorry

  /-- The function returns r for nums and r' for dedup(nums), and r = r'.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). Let dedup(nums) be the sequence obtained by starting with nums[0] and, for each i from 1 to len(nums)-1, appending nums[i] if nums[i] != nums[i-1]. -/
  theorem spec_11 (nums nums' : Slice I64) (h : ValidInput nums)
      (hdedup : vals nums' = dedup (vals nums)) :
      ∃ r r' : I64, wiggle_max_length nums = ok r ∧ wiggle_max_length nums' = ok r' ∧ r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice I64) (h : ValidInput nums)
        (hdedup : vals nums' = dedup (vals nums)), ∃ r r' : I64, wiggle_max_length nums = ok r ∧ wiggle_max_length nums' = ok r' ∧ r = r') := by
    sorry

  /-- The function returns r. If all elements of nums are equal, then r = 1. Otherwise, let nums' = dedup(nums) (as defined in spec_11), let m = len(nums') (so m >= 2), and for each i with 0 <= i <= m-2 let d_i = nums'[i+1] - nums'[i]. All d_i are non-zero. Let c be the number of indices i with 1 <= i <= m-2 such that d_i and d_{i-1} have opposite signs (i.e., (d_i > 0 and d_{i-1} < 0) or (d_i < 0 and d_{i-1} > 0)). Then r = c + 2.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_12 (nums : Slice I64) (h : ValidInput nums) :
      ∃ r : I64, wiggle_max_length nums = ok r ∧
        (AllEqual (vals nums) → r.val = 1) ∧
        (¬ AllEqual (vals nums) →
          r.val = ((countSignFlips (diffs (dedup (vals nums))) : ℕ) : ℤ) + 2) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums), ∃ r : I64, wiggle_max_length nums = ok r ∧
          (AllEqual (vals nums) → r.val = 1) ∧
          (¬ AllEqual (vals nums) →
            r.val = ((countSignFlips (diffs (dedup (vals nums))) : ℕ) : ℤ) + 2)) := by
    sorry

  /-- If len(nums) >= 2 and nums is non-decreasing (i.e., nums[i] <= nums[i+1] for all 0 <= i < len(nums)-1) or non-increasing (i.e., nums[i] >= nums[i+1] for all 0 <= i < len(nums)-1), then the function returns r = 1 if all elements of nums are equal, and r = 2 otherwise.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_13 (nums : Slice I64) (h : ValidInput nums) (hlen : 2 ≤ nums.val.length)
      (hmono : Nondecreasing (vals nums) ∨ Nonincreasing (vals nums)) :
      ∃ r : I64, wiggle_max_length nums = ok r ∧
        (AllEqual (vals nums) → r.val = 1) ∧
        (¬ AllEqual (vals nums) → r.val = 2) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (hlen : 2 ≤ nums.val.length)
        (hmono : Nondecreasing (vals nums) ∨ Nonincreasing (vals nums)), ∃ r : I64, wiggle_max_length nums = ok r ∧
          (AllEqual (vals nums) → r.val = 1) ∧
          (¬ AllEqual (vals nums) → r.val = 2)) := by
    sorry

  /-- If len(nums) = 3, then the function returns r = 3 if (nums[1] - nums[0]) * (nums[2] - nums[1]) < 0; otherwise, r = 2 if nums[0], nums[1], nums[2] are not all equal, and r = 1 if they are all equal.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 1000 and 0 <= nums[i] <= 1000 for all 0 <= i < len(nums). -/
  theorem spec_14 (nums : Slice I64) (h : ValidInput nums) (hlen : nums.val.length = 3) :
      ∃ r : I64, wiggle_max_length nums = ok r ∧
        ∀ a b c : ℤ, vals nums = [a, b, c] →
          (((b - a) * (c - b) < 0) → r.val = 3) ∧
          (¬ ((b - a) * (c - b) < 0) → (¬(a = b ∧ b = c) → r.val = 2)) ∧
          ((a = b ∧ b = c) → r.val = 1) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (hlen : nums.val.length = 3), ∃ r : I64, wiggle_max_length nums = ok r ∧
          ∀ a b c : ℤ, vals nums = [a, b, c] →
            (((b - a) * (c - b) < 0) → r.val = 3) ∧
            (¬ ((b - a) * (c - b) < 0) → (¬(a = b ∧ b = c) → r.val = 2)) ∧
            ((a = b ∧ b = c) → r.val = 1)) := by
    sorry

  end AegisSpec.WiggleMaxLength
