import Aegis.SplitArraySameAverage.Code.Funs

/-!
# Specifications of `Aegis.SplitArraySameAverage.split_array_same_average`

LeetCode problem `split-array-with-same-average`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SplitArraySameAverage

  def size (nums : Slice Std.I64) : Nat := (Slice.len nums).val

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def valAt (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

  def total (nums : Slice Std.I64) : Int := (vals nums).sum

  def idxSum (nums : Slice Std.I64) (I : Finset Nat) : Int :=
    I.sum (fun i => valAt nums i)

  def InRange (nums : Slice Std.I64) : Prop :=
    ∀ i : Nat, i < size nums → 0 ≤ valAt nums i ∧ valAt nums i ≤ 10000

  def IsSplittingIndexSet (nums : Slice Std.I64) (I : Finset Nat) : Prop :=
    I ⊆ Finset.range (size nums) ∧
      I.Nonempty ∧
      I ≠ Finset.range (size nums) ∧
      idxSum nums I * (size nums : Int) = (I.card : Int) * total nums

  def IsSmallSplittingIndexSet (nums : Slice Std.I64) (I : Finset Nat) : Prop :=
    I ⊆ Finset.range (size nums) ∧
      1 ≤ I.card ∧
      2 * I.card ≤ size nums ∧
      idxSum nums I * (size nums : Int) = (I.card : Int) * total nums

  /-- Let T = nums[0] + ... + nums[n-1]. Whenever split_array_same_average(nums) returns a result r, we have r = true if and only if there exists a set of indices I such that: (a) I is a subset of {0,1,...,n-1}; (b) I is non-empty; (c) I is not the whole index set; and (d) (sum_{i in I} nums[i]) * n = |I| * T. If no such I exists, then r = false.
    Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 30 and, for every i with 0 <= i < n, 0 <= nums[i] <= 10000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hn_lo : 1 ≤ size nums) (hn_hi : size nums ≤ 30)
      (hbnd : InRange nums)
      (r : Bool)
      (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r) :
      (r = true ↔ ∃ I : Finset Nat, IsSplittingIndexSet nums I) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_lo : 1 ≤ size nums) (hn_hi : size nums ≤ 30)
        (hbnd : InRange nums)
        (r : Bool)
        (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r), (r = true ↔ ∃ I : Finset Nat, IsSplittingIndexSet nums I)) := by
    sorry

  /-- For every such input, split_array_same_average(nums) returns a result r : Bool; it does not fail, panic, overflow, or index out of bounds.
    Preconditions: Let n = len(nums). The slice satisfies 1 <= n <= 30 and, for every i with 0 <= i < n, 0 <= nums[i] <= 10000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hn_lo : 1 ≤ size nums) (hn_hi : size nums ≤ 30)
      (hbnd : InRange nums) :
      ∃ r : Bool, Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_lo : 1 ≤ size nums) (hn_hi : size nums ≤ 30)
        (hbnd : InRange nums), ∃ r : Bool, Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r) := by
    sorry

  /-- Whenever split_array_same_average(nums) returns a result r, r = false.
    Preconditions: n = len(nums) = 1 and 0 <= nums[0] <= 10000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hn : size nums = 1)
      (hbnd : 0 ≤ valAt nums 0 ∧ valAt nums 0 ≤ 10000)
      (r : Bool)
      (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r) :
      r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : size nums = 1)
        (hbnd : 0 ≤ valAt nums 0 ∧ valAt nums 0 ≤ 10000)
        (r : Bool)
        (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r), r = false) := by
    sorry

  /-- Whenever split_array_same_average(nums) returns a result r, r = true if and only if nums[0] = nums[1].
    Preconditions: n = len(nums) = 2 and 0 <= nums[0] <= 10000 and 0 <= nums[1] <= 10000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hn : size nums = 2)
      (hbnd0 : 0 ≤ valAt nums 0 ∧ valAt nums 0 ≤ 10000)
      (hbnd1 : 0 ≤ valAt nums 1 ∧ valAt nums 1 ≤ 10000)
      (r : Bool)
      (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r) :
      (r = true ↔ valAt nums 0 = valAt nums 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : size nums = 2)
        (hbnd0 : 0 ≤ valAt nums 0 ∧ valAt nums 0 ≤ 10000)
        (hbnd1 : 0 ≤ valAt nums 1 ∧ valAt nums 1 ≤ 10000)
        (r : Bool)
        (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r), (r = true ↔ valAt nums 0 = valAt nums 1)) := by
    sorry

  /-- Whenever split_array_same_average(nums) returns a result r, r = true if and only if there exists an index i in {0,1,2} such that nums[i] * 3 = T.
    Preconditions: n = len(nums) = 3 and 0 <= nums[i] <= 10000 for i = 0,1,2. Let T = nums[0] + nums[1] + nums[2]. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hn : size nums = 3)
      (hbnd : ∀ i : Nat, i < 3 → 0 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
      (r : Bool)
      (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r) :
      (r = true ↔ ∃ i : Nat, i < 3 ∧ valAt nums i * 3 = total nums) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn : size nums = 3)
        (hbnd : ∀ i : Nat, i < 3 → 0 ≤ valAt nums i ∧ valAt nums i ≤ 10000)
        (r : Bool)
        (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r), (r = true ↔ ∃ i : Nat, i < 3 ∧ valAt nums i * 3 = total nums)) := by
    sorry

  /-- Whenever split_array_same_average(nums) returns a result r, r = true.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 2 <= n <= 30, 0 <= nums[i] <= 10000 for all i, and there exists an index j with 0 <= j < n such that nums[j] * n = T. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hn_lo : 2 ≤ size nums) (hn_hi : size nums ≤ 30)
      (hbnd : InRange nums)
      (j : Nat) (hj : j < size nums)
      (hwit : valAt nums j * (size nums : Int) = total nums)
      (r : Bool)
      (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r) :
      r = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_lo : 2 ≤ size nums) (hn_hi : size nums ≤ 30)
        (hbnd : InRange nums)
        (j : Nat) (hj : j < size nums)
        (hwit : valAt nums j * (size nums : Int) = total nums)
        (r : Bool)
        (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r), r = true) := by
    sorry

  /-- Whenever split_array_same_average(nums) returns a result r with r = true, there exists a set of indices I such that: I is a subset of {0,...,n-1}, 1 <= |I|, 2*|I| <= n, and (sum_{i in I} nums[i]) * n = |I| * T.
    Preconditions: Let n = len(nums) and T = sum_{i=0}^{n-1} nums[i]. Assume 2 <= n <= 30 and 0 <= nums[i] <= 10000 for all i. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hn_lo : 2 ≤ size nums) (hn_hi : size nums ≤ 30)
      (hbnd : InRange nums)
      (r : Bool)
      (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r)
      (hr_true : r = true) :
      ∃ I : Finset Nat, IsSmallSplittingIndexSet nums I := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_lo : 2 ≤ size nums) (hn_hi : size nums ≤ 30)
        (hbnd : InRange nums)
        (r : Bool)
        (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r)
        (hr_true : r = true), ∃ I : Finset Nat, IsSmallSplittingIndexSet nums I) := by
    sorry

  /-- Whenever split_array_same_average(nums) returns r and split_array_same_average(nums') returns r', we have r = r'.
    Preconditions: Let nums and nums' be two slices, each satisfying 1 <= len <= 30 and all entries in [0,10000], with len(nums) = len(nums') = n. Assume there is a bijection phi : {0,...,n-1} -> {0,...,n-1} such that nums'[i] = nums[phi(i)] for every i; thus nums' is a permutation of nums. -/
  theorem spec_8 (nums nums' : Slice Std.I64)
      (hnums_lo : 1 ≤ size nums) (hnums_hi : size nums ≤ 30)
      (hnums'_lo : 1 ≤ size nums') (hnums'_hi : size nums' ≤ 30)
      (hbnd : InRange nums) (hbnd' : InRange nums')
      (hlen : size nums' = size nums)
      (φ : Equiv.Perm (Fin (size nums)))
      (hφ : ∀ i : Fin (size nums), valAt nums' i.val = valAt nums (φ i).val)
      (r r' : Bool)
      (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r)
      (hr' : Aegis.SplitArraySameAverage.split_array_same_average nums' = Result.ok r') :
      r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hnums_lo : 1 ≤ size nums) (hnums_hi : size nums ≤ 30)
        (hnums'_lo : 1 ≤ size nums') (hnums'_hi : size nums' ≤ 30)
        (hbnd : InRange nums) (hbnd' : InRange nums')
        (hlen : size nums' = size nums)
        (φ : Equiv.Perm (Fin (size nums)))
        (hφ : ∀ i : Fin (size nums), valAt nums' i.val = valAt nums (φ i).val)
        (r r' : Bool)
        (hr : Aegis.SplitArraySameAverage.split_array_same_average nums = Result.ok r)
        (hr' : Aegis.SplitArraySameAverage.split_array_same_average nums' = Result.ok r'), r = r') := by
    sorry

  end AegisSpec.SplitArraySameAverage
