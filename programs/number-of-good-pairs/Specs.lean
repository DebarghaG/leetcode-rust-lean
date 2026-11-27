import Aegis.NumIdenticalPairs.Code.Funs

/-!
# Specifications of `Aegis.NumIdenticalPairs.num_identical_pairs`

LeetCode problem `number-of-good-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NumIdenticalPairs

  namespace AegisSpec.NumIdenticalPairs

  def valAt (l : List Std.I64) (i : ℕ) : Option ℤ := l[i]?.map (fun x => x.val)

  def occCount (l : List Std.I64) (v : ℤ) : ℕ :=
    ((Finset.range l.length).filter (fun i => valAt l i = some v)).card

  def numPairs (l : List Std.I64) : ℕ :=
    (((Finset.range l.length).product (Finset.range l.length)).filter
        (fun p => p.1 < p.2 ∧ valAt l p.1 = valAt l p.2)).card

  def pairSum (l : List Std.I64) : ℕ :=
    ∑ k ∈ Finset.Icc (1 : ℕ) 100, occCount l (k : ℤ) * (occCount l (k : ℤ) - 1) / 2

  /-- For every input satisfying the preconditions, the function returns a result r and r = |{(i,j) : 0 <= i < j < len(nums) and nums[i] = nums[j]}|; that is, r is exactly the number of 0-indexed index pairs (i,j) with i < j whose entries are equal.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100) :
      ∃ r : Std.I64, num_identical_pairs nums = ok r ∧ r.val = (numPairs nums.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100), ∃ r : Std.I64, num_identical_pairs nums = ok r ∧ r.val = (numPairs nums.val : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r and does not fail (no panic, out-of-bounds access, or i64 overflow).
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100) :
      ∃ r : Std.I64, num_identical_pairs nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100), ∃ r : Std.I64, num_identical_pairs nums = ok r) := by
    sorry

  /-- For every input satisfying the preconditions, whenever the function returns a result r, 0 <= r.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (r : Std.I64) (hr : num_identical_pairs nums = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (r : Std.I64) (hr : num_identical_pairs nums = ok r), 0 ≤ r.val) := by
    sorry

  /-- For every input satisfying the preconditions, whenever the function returns a result r, r <= len(nums)*(len(nums)-1)/2.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (r : Std.I64) (hr : num_identical_pairs nums = ok r) :
      r.val ≤ ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (r : Std.I64) (hr : num_identical_pairs nums = ok r), r.val ≤ ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, whenever the function returns a result r, r = 0 if and only if for every i and j with 0 <= i < j < len(nums), nums[i] != nums[j].
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (r : Std.I64) (hr : num_identical_pairs nums = ok r) :
      (r.val = 0 ↔
        ∀ (i j : ℕ) (_ : i < j) (_ : j < nums.val.length),
          nums.val[i].val ≠ nums.val[j].val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (r : Std.I64) (hr : num_identical_pairs nums = ok r), (r.val = 0 ↔
          ∀ (i j : ℕ) (_ : i < j) (_ : j < nums.val.length),
            nums.val[i].val ≠ nums.val[j].val)) := by
    sorry

  /-- For every input satisfying the preconditions with len(nums) = 2, whenever the function returns a result r, r = 1 if nums[0] = nums[1], and r = 0 otherwise.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (hlen : nums.val.length = 2)
      (r : Std.I64) (hr : num_identical_pairs nums = ok r) :
      (nums.val[0].val = nums.val[1].val → r.val = 1) ∧
        (nums.val[0].val ≠ nums.val[1].val → r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (hlen : nums.val.length = 2)
        (r : Std.I64) (hr : num_identical_pairs nums = ok r), (nums.val[0].val = nums.val[1].val → r.val = 1) ∧
          (nums.val[0].val ≠ nums.val[1].val → r.val = 0)) := by
    sorry

  /-- For every input satisfying the preconditions, if all entries of nums are equal (there is a value v such that nums[i] = v for every i with 0 <= i < len(nums)), then whenever the function returns a result r, r = len(nums)*(len(nums)-1)/2.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (v : ℤ) (hconst : ∀ (i : ℕ) (_ : i < nums.val.length), nums.val[i].val = v)
      (r : Std.I64) (hr : num_identical_pairs nums = ok r) :
      r.val = ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (v : ℤ) (hconst : ∀ (i : ℕ) (_ : i < nums.val.length), nums.val[i].val = v)
        (r : Std.I64) (hr : num_identical_pairs nums = ok r), r.val = ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, whenever the function returns a result r, let c_v = |{i : 0 <= i < len(nums) and nums[i] = v}| for each integer v with 1 <= v <= 100. Then r = sum_{v=1}^{100} c_v*(c_v-1)/2.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (r : Std.I64) (hr : num_identical_pairs nums = ok r) :
      r.val = (pairSum nums.val : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (r : Std.I64) (hr : num_identical_pairs nums = ok r), r.val = (pairSum nums.val : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, whenever the function returns a result r, for every integer v with 1 <= v <= 100, if c_v = |{i : 0 <= i < len(nums) and nums[i] = v}|, then r >= c_v*(c_v-1)/2.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (r : Std.I64) (hr : num_identical_pairs nums = ok r)
      (v : ℤ) (hv1 : 1 ≤ v) (hv2 : v ≤ 100) :
      ((occCount nums.val v * (occCount nums.val v - 1) / 2 : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (r : Std.I64) (hr : num_identical_pairs nums = ok r)
        (v : ℤ) (hv1 : 1 ≤ v) (hv2 : v ≤ 100), ((occCount nums.val v * (occCount nums.val v - 1) / 2 : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- For every two inputs nums and nums' satisfying the preconditions, if nums' is a rearrangement of nums (equivalently, for every integer v with 1 <= v <= 100, the number of occurrences of v in nums equals the number of occurrences of v in nums'), then whenever the function returns r on nums and r' on nums', we have r = r'.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_10 (nums nums' : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (hlo' : 1 ≤ nums'.val.length) (hhi' : nums'.val.length ≤ 100)
      (hval' : ∀ (i : ℕ) (_ : i < nums'.val.length),
        1 ≤ nums'.val[i].val ∧ nums'.val[i].val ≤ 100)
      (hperm : ∀ (v : ℤ), 1 ≤ v → v ≤ 100 → occCount nums.val v = occCount nums'.val v)
      (r r' : Std.I64)
      (hr : num_identical_pairs nums = ok r) (hr' : num_identical_pairs nums' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (hlo' : 1 ≤ nums'.val.length) (hhi' : nums'.val.length ≤ 100)
        (hval' : ∀ (i : ℕ) (_ : i < nums'.val.length),
          1 ≤ nums'.val[i].val ∧ nums'.val[i].val ≤ 100)
        (hperm : ∀ (v : ℤ), 1 ≤ v → v ≤ 100 → occCount nums.val v = occCount nums'.val v)
        (r r' : Std.I64)
        (hr : num_identical_pairs nums = ok r) (hr' : num_identical_pairs nums' = ok r'), r.val = r'.val) := by
    sorry

  /-- For every input nums satisfying the preconditions, every x with 1 <= x <= 100 and len(nums) < 100, let c_x = |{i : 0 <= i < len(nums) and nums[i] = x}|. Whenever the function returns r on nums and r' on the slice obtained by appending x to nums, we have r' = r + c_x.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (x : Std.I64) (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 100) (hlen : nums.val.length < 100)
      (nums' : Slice Std.I64) (hnums' : nums'.val = nums.val ++ [x])
      (r r' : Std.I64)
      (hr : num_identical_pairs nums = ok r) (hr' : num_identical_pairs nums' = ok r') :
      r'.val = r.val + (occCount nums.val x.val : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (x : Std.I64) (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 100) (hlen : nums.val.length < 100)
        (nums' : Slice Std.I64) (hnums' : nums'.val = nums.val ++ [x])
        (r r' : Std.I64)
        (hr : num_identical_pairs nums = ok r) (hr' : num_identical_pairs nums' = ok r'), r'.val = r.val + (occCount nums.val x.val : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, if exactly one value occurs twice in nums and every other value occurs at most once (i.e., c_v = 2 for exactly one v, and c_w <= 1 for all w != v), then whenever the function returns a result r, r = 1.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (v : ℤ) (hv1 : 1 ≤ v) (hv2 : v ≤ 100)
      (hvtwice : occCount nums.val v = 2)
      (hothers : ∀ (w : ℤ), 1 ≤ w → w ≤ 100 → w ≠ v → occCount nums.val w ≤ 1)
      (r : Std.I64) (hr : num_identical_pairs nums = ok r) :
      r.val = 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (v : ℤ) (hv1 : 1 ≤ v) (hv2 : v ≤ 100)
        (hvtwice : occCount nums.val v = 2)
        (hothers : ∀ (w : ℤ), 1 ≤ w → w ≤ 100 → w ≠ v → occCount nums.val w ≤ 1)
        (r : Std.I64) (hr : num_identical_pairs nums = ok r), r.val = 1) := by
    sorry

  /-- For every input satisfying the preconditions with len(nums) = 1, whenever the function returns a result r, r = 0.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_13 (nums : Slice Std.I64)
      (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
      (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
        1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
      (hlen : nums.val.length = 1)
      (r : Std.I64) (hr : num_identical_pairs nums = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlo : 1 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
        (hval : ∀ (i : ℕ) (_ : i < nums.val.length),
          1 ≤ nums.val[i].val ∧ nums.val[i].val ≤ 100)
        (hlen : nums.val.length = 1)
        (r : Std.I64) (hr : num_identical_pairs nums = ok r), r.val = 0) := by
    sorry

  /-- There exists an input satisfying the preconditions for which the function returns r = 4950; explicitly, if nums has length 100 and nums[i] = 100 for every i with 0 <= i < 100, then the function returns r = 4950.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_14 :
      (∃ nums : Slice Std.I64,
          nums.val.length = 100 ∧
            (∀ (i : ℕ) (_ : i < nums.val.length), nums.val[i].val = 100) ∧
            num_identical_pairs nums = ok 4950#i64) ∧
        (∀ (nums : Slice Std.I64),
          nums.val.length = 100 →
            (∀ (i : ℕ) (_ : i < nums.val.length), nums.val[i].val = 100) →
            num_identical_pairs nums = ok 4950#i64) := by
    sorry

  theorem spec_14_neg :
      ¬ ((∃ nums : Slice Std.I64,
            nums.val.length = 100 ∧
              (∀ (i : ℕ) (_ : i < nums.val.length), nums.val[i].val = 100) ∧
              num_identical_pairs nums = ok 4950#i64) ∧
          (∀ (nums : Slice Std.I64),
            nums.val.length = 100 →
              (∀ (i : ℕ) (_ : i < nums.val.length), nums.val[i].val = 100) →
              num_identical_pairs nums = ok 4950#i64)) := by
    sorry

  end AegisSpec.NumIdenticalPairs
