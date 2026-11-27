import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `sorting-three-groups`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Classical

  open Aegis.MinimumOperations

  namespace AegisSpec.MinimumOperations

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def elemAt (nums : Slice Std.I64) (i : ℕ) : Int := (vals nums).getD i 0

  def countIn (nums : Slice Std.I64) (v : Int) (lo hi : ℕ) : ℕ :=
    ((List.range hi).filter
        (fun i => decide (lo ≤ i) && decide (elemAt nums i = v))).length

  def countVal (nums : Slice Std.I64) (v : Int) : ℕ := countIn nums v 0 nums.val.length

  def cover (nums : Slice Std.I64) (a b : ℕ) : ℕ :=
    countIn nums 1 0 a + countIn nums 2 a b + countIn nums 3 b nums.val.length

  def maxCover (nums : Slice Std.I64) : ℕ :=
    (List.range (nums.val.length + 1)).foldr
      (fun a acc =>
        (List.range (nums.val.length + 1)).foldr
          (fun b acc' => if a ≤ b then max acc' (cover nums a b) else acc') acc)
      0

  def Nondecreasing (nums : Slice Std.I64) : Prop := (vals nums).Pairwise (· ≤ ·)

  def Nonincreasing (nums : Slice Std.I64) : Prop := (vals nums).Pairwise (· ≥ ·)

  def IsNDSubseq (nums : Slice Std.I64) (idx : List ℕ) : Prop :=
    idx.Pairwise (· < ·) ∧ (∀ i, i ∈ idx → i < nums.val.length) ∧
      (idx.map (elemAt nums)).Pairwise (· ≤ ·)

  noncomputable def maxNDSubseqLen (nums : Slice Std.I64) : ℕ :=
    (List.range (nums.val.length + 1)).foldr
      (fun k acc =>
        if ∃ idx : List ℕ, idx.length = k ∧ IsNDSubseq nums idx then max acc k else acc)
      0

  def maxOneThree (nums : Slice Std.I64) : ℕ :=
    (List.range (nums.val.length + 1)).foldr
      (fun a acc => max acc (countIn nums 1 0 a + countIn nums 3 a nums.val.length)) 0

  def maxCountVal (nums : Slice Std.I64) : ℕ :=
    max (countVal nums 1) (max (countVal nums 2) (countVal nums 3))

  def entries123 (nums : Slice Std.I64) : Prop :=
    ∀ i, i < nums.val.length → elemAt nums i = 1 ∨ elemAt nums i = 2 ∨ elemAt nums i = 3

  def sliceOfList (l : List Std.I64) (h : l.length ≤ Usize.max) : Slice Std.I64 where
    leng := l.length
    list := Aeneas.Data.ListN.ListN.fromList l
    bound := h

  def subSlice (nums : Slice Std.I64) (i j : ℕ) : Slice Std.I64 :=
    sliceOfList ((nums.val.drop i).take (j - i)) (by
      have h₁ : ((nums.val.drop i).take (j - i)).length ≤ (nums.val.drop i).length := by
        rw [List.length_take]; exact Nat.min_le_right ..
      have h₂ : (nums.val.drop i).length ≤ nums.val.length := by
        rw [List.length_drop]; exact Nat.sub_le ..
      have h₃ : nums.val.length ≤ Usize.max := by
        have h₄ : nums.val.length = nums.leng := by
          simp [Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN_length]
        rw [h₄]; exact nums.bound
      exact Nat.le_trans h₁ (Nat.le_trans h₂ h₃))

  /-- Let n = len(nums). For integers a and b with 0 <= a <= b <= n, define C(a,b) to be the number of indices i with 0 <= i < a and nums[i] = 1, plus the number of indices i with a <= i < b and nums[i] = 2, plus the number of indices i with b <= i < n and nums[i] = 3. The function returns a result r and r = n - max{C(a,b) | 0 <= a <= b <= n}.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_1 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      ∃ r : Std.I64, minimum_operations nums = ok r ∧
        r.val = (nums.val.length : ℤ) - (maxCover nums : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
          r.val = (nums.val.length : ℤ) - (maxCover nums : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_2 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      ∃ r : Std.I64, minimum_operations nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), ∃ r : Std.I64, minimum_operations nums = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= len(nums).
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_3 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      ∃ r : Std.I64, minimum_operations nums = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
          0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Let L be the maximum length of a non-decreasing subsequence of nums, i.e. the maximum k >= 0 for which there exist indices 0 <= i_1 < ... < i_k < len(nums) with nums[i_1] <= ... <= nums[i_k] (k = 0 is allowed). The function returns a result r and r = len(nums) - L.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_4 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      ∃ r : Std.I64, minimum_operations nums = ok r ∧
        r.val = (nums.val.length : ℤ) - (maxNDSubseqLen nums : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
          r.val = (nums.val.length : ℤ) - (maxNDSubseqLen nums : ℤ)) := by
    sorry

  /-- The function returns a result r and there exists a (possibly empty) sequence of indices 0 <= i_1 < ... < i_{len(nums)-r} < len(nums) such that nums[i_1] <= ... <= nums[i_{len(nums)-r}]. When len(nums)-r = 0, the condition is that the empty sequence is allowed.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_5 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      ∃ r : Std.I64, minimum_operations nums = ok r ∧
        ∃ idx : List ℕ, IsNDSubseq nums idx ∧
          (idx.length : ℤ) = (nums.val.length : ℤ) - r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
          ∃ idx : List ℕ, IsNDSubseq nums idx ∧
            (idx.length : ℤ) = (nums.val.length : ℤ) - r.val) := by
    sorry

  /-- The function returns a result r and every non-decreasing subsequence of nums has length at most len(nums)-r. A non-decreasing subsequence here is a sequence of indices 0 <= i_1 < ... < i_k < len(nums) with nums[i_1] <= ... <= nums[i_k], where k = 0 is allowed.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_6 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      ∃ r : Std.I64, minimum_operations nums = ok r ∧
        ∀ idx : List ℕ, IsNDSubseq nums idx →
          (idx.length : ℤ) ≤ (nums.val.length : ℤ) - r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
          ∀ idx : List ℕ, IsNDSubseq nums idx →
            (idx.length : ℤ) ≤ (nums.val.length : ℤ) - r.val) := by
    sorry

  /-- The function returns a result r and there exist integers a,b with 0 <= a <= b <= len(nums) such that r = len(nums) - C(a,b), where C(a,b) is the number of indices i with 0 <= i < a and nums[i]=1, plus the number of indices i with a <= i < b and nums[i]=2, plus the number of indices i with b <= i < len(nums) and nums[i]=3.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_7 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      ∃ r : Std.I64, minimum_operations nums = ok r ∧
        ∃ a b : ℕ, a ≤ b ∧ b ≤ nums.val.length ∧
          r.val = (nums.val.length : ℤ) - (cover nums a b : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
          ∃ a b : ℕ, a ≤ b ∧ b ≤ nums.val.length ∧
            r.val = (nums.val.length : ℤ) - (cover nums a b : ℤ)) := by
    sorry

  /-- The function returns a result r and for every pair of integers a,b with 0 <= a <= b <= len(nums), r <= len(nums) - C(a,b), where C(a,b) is the number of indices i with 0 <= i < a and nums[i]=1, plus the number of indices i with a <= i < b and nums[i]=2, plus the number of indices i with b <= i < len(nums) and nums[i]=3.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_8 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      ∃ r : Std.I64, minimum_operations nums = ok r ∧
        ∀ a b : ℕ, a ≤ b → b ≤ nums.val.length →
          r.val ≤ (nums.val.length : ℤ) - (cover nums a b : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
          ∀ a b : ℕ, a ≤ b → b ≤ nums.val.length →
            r.val ≤ (nums.val.length : ℤ) - (cover nums a b : ℤ)) := by
    sorry

  /-- Let c1, c2, c3 be the numbers of occurrences of 1, 2, and 3 in nums, respectively. The function returns a result r and r <= len(nums) - max(c1,c2,c3).
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_9 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      ∃ r : Std.I64, minimum_operations nums = ok r ∧
        r.val ≤ (nums.val.length : ℤ) - (maxCountVal nums : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧
          r.val ≤ (nums.val.length : ℤ) - (maxCountVal nums : ℤ)) := by
    sorry

  /-- If nums[0] <= nums[1] <= ... <= nums[len(nums)-1], then the function returns a result r with r = 0.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_10 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      Nondecreasing nums → ∃ r : Std.I64, minimum_operations nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), Nondecreasing nums → ∃ r : Std.I64, minimum_operations nums = ok r ∧ r.val = 0) := by
    sorry

  /-- If nums[0] >= nums[1] >= ... >= nums[len(nums)-1], and c1,c2,c3 are the numbers of occurrences of 1,2,3 in nums, then the function returns a result r with r = len(nums) - max(c1,c2,c3).
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_11 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      Nonincreasing nums → ∃ r : Std.I64, minimum_operations nums = ok r ∧
        r.val = (nums.val.length : ℤ) - (maxCountVal nums : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), Nonincreasing nums → ∃ r : Std.I64, minimum_operations nums = ok r ∧
          r.val = (nums.val.length : ℤ) - (maxCountVal nums : ℤ)) := by
    sorry

  /-- If no element of nums equals 2, then the function returns a result r with r = len(nums) - max over integers a satisfying 0 <= a <= len(nums) of (the number of indices i with 0 <= i < a and nums[i]=1 plus the number of indices i with a <= i < len(nums) and nums[i]=3).
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_12 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      (∀ i, i < nums.val.length → elemAt nums i ≠ 2) →
        ∃ r : Std.I64, minimum_operations nums = ok r ∧
          r.val = (nums.val.length : ℤ) - (maxOneThree nums : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), (∀ i, i < nums.val.length → elemAt nums i ≠ 2) →
          ∃ r : Std.I64, minimum_operations nums = ok r ∧
            r.val = (nums.val.length : ℤ) - (maxOneThree nums : ℤ)) := by
    sorry

  /-- If nums[0] = 1, then the function returns a result r and r equals the result of the same function on the slice nums[1:len(nums)].
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_13 (nums : Slice Std.I64) (h₁ : 2 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      elemAt nums 0 = 1 →
        ∃ r : Std.I64, minimum_operations nums = ok r ∧
          minimum_operations (subSlice nums 1 nums.val.length) = ok r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 2 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), elemAt nums 0 = 1 →
          ∃ r : Std.I64, minimum_operations nums = ok r ∧
            minimum_operations (subSlice nums 1 nums.val.length) = ok r) := by
    sorry

  /-- If nums[len(nums)-1] = 3, then the function returns a result r and r equals the result of the same function on the slice nums[0:len(nums)-1].
    Preconditions: len(nums) >= 2, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_14 (nums : Slice Std.I64) (h₁ : 2 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      elemAt nums (nums.val.length - 1) = 3 →
        ∃ r : Std.I64, minimum_operations nums = ok r ∧
          minimum_operations (subSlice nums 0 (nums.val.length - 1)) = ok r := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 2 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), elemAt nums (nums.val.length - 1) = 3 →
          ∃ r : Std.I64, minimum_operations nums = ok r ∧
            minimum_operations (subSlice nums 0 (nums.val.length - 1)) = ok r) := by
    sorry

  /-- The function returns a result r and, if r = 0, then nums[0] <= nums[1] <= ... <= nums[len(nums)-1].
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every integer i with 0 <= i < len(nums), nums[i] is 1, 2, or 3. -/
  theorem spec_15 (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
      (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums) :
      ∃ r : Std.I64, minimum_operations nums = ok r ∧ (r.val = 0 → Nondecreasing nums) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64) (h₁ : 1 ≤ nums.val.length)
        (h₂ : nums.val.length ≤ 100) (h₃ : entries123 nums), ∃ r : Std.I64, minimum_operations nums = ok r ∧ (r.val = 0 → Nondecreasing nums)) := by
    sorry

  end AegisSpec.MinimumOperations
