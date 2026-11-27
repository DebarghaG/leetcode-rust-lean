import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-total-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinOperations

def EntriesInRange (l : List I64) : Prop :=
  ∀ (i : Nat) (hi : i < l.length),
    -1000000000 ≤ (l.get ⟨i, hi⟩).val ∧ (l.get ⟨i, hi⟩).val ≤ 1000000000

def ValidInput (nums : Slice I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧ EntriesInRange nums.val

def asInts (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def AdjacentDiffCount (l : List I64) : Nat :=
  ((l.zip (l.drop 1)).filter (fun p => p.1.val ≠ p.2.val)).length

def AllEq (l : List I64) : Prop :=
  ∀ (i : Nat) (j : Nat) (hi : i < l.length) (hj : j < l.length),
    (l.get ⟨i, hi⟩).val = (l.get ⟨j, hj⟩).val

def AllAdjacentDiff (l : List I64) : Prop :=
  ∀ (i : Nat) (hi : i < l.length - 1),
    (l.get ⟨i, by omega⟩).val ≠ (l.get ⟨i + 1, by omega⟩).val

def Nondecreasing (l : List I64) : Prop :=
  ∀ (i : Nat) (hi : i < l.length - 1),
    (l.get ⟨i, by omega⟩).val ≤ (l.get ⟨i + 1, by omega⟩).val

def DistinctCount (l : List I64) : Nat := (l.map (fun x => x.val)).dedup.length

def Compress (vals : List Int) : List Int :=
  (vals.foldl
    (fun (acc : List Int) (x : Int) =>
      match acc with
      | [] => [x]
      | y :: ys => if y = x then y :: ys else x :: y :: ys)
    []).reverse

def Expand (vals : List Int) (m : Nat) : List Int :=
  vals.flatMap (fun x => List.replicate m x)

structure Op where

  p : Nat

  k : Int

def applyOp (vals : List Int) (op : Op) : List Int :=
  (vals.take op.p).map (fun x => x + op.k) ++ vals.drop op.p

def IsConstant (vals : List Int) : Prop := ∀ x ∈ vals, ∀ y ∈ vals, x = y

def EqualizableIn (vals : List Int) (k : Nat) : Prop :=
  ∃ ops : List Op,
    ops.length = k ∧
      (∀ op ∈ ops, 1 ≤ op.p ∧ op.p ≤ vals.length) ∧ IsConstant (ops.foldl applyOp vals)

/-- The function returns a result r, and r equals the number of indices i with 0 <= i < len(nums)-1 such that nums[i] != nums[i+1]. Equivalently, r is the minimum number of operations needed to make all elements of nums equal, where one operation chooses a prefix length p with 1 <= p <= len(nums) and an integer k and adds k to every element in positions 0 through p-1.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice I64) (h : ValidInput nums) :
    ∃ r : I64,
      Aegis.MinOperations.min_operations nums = ok r ∧
        r.val = (AdjacentDiffCount nums.val : Int) ∧
          ∀ (k : Nat), EqualizableIn (asInts nums) k ↔ AdjacentDiffCount nums.val ≤ k := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums), ∃ r : I64,
      Aegis.MinOperations.min_operations nums = ok r ∧
        r.val = (AdjacentDiffCount nums.val : Int) ∧
          ∀ (k : Nat), EqualizableIn (asInts nums) k ↔ AdjacentDiffCount nums.val ≤ k) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, go out of bounds, or panic).
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice I64) (h : ValidInput nums) :
    ∃ r : I64, Aegis.MinOperations.min_operations nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums), ∃ r : I64, Aegis.MinOperations.min_operations nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice I64) (h : ValidInput nums) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r) : 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(nums)-1.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice I64) (h : ValidInput nums) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r) :
    r.val ≤ (nums.val.length : Int) - 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r), r.val ≤ (nums.val.length : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i and j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] = nums[j].
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice I64) (h : ValidInput nums) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r) :
    (r.val = 0 ↔ AllEq nums.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r), (r.val = 0 ↔ AllEq nums.val)) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums)-1 if and only if for every i with 0 <= i < len(nums)-1, nums[i] != nums[i+1].
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice I64) (h : ValidInput nums) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r) :
    (r.val = (nums.val.length : Int) - 1 ↔ AllAdjacentDiff nums.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r), (r.val = (nums.val.length : Int) - 1 ↔ AllAdjacentDiff nums.val)) := by
  sorry

/-- For every integer c and every slice nums2 with len(nums2) = len(nums) and nums2[i] = nums[i] + c for all 0 <= i < len(nums), and with -1000000000 <= nums2[i] <= 1000000000 for all such i, if min_operations(nums) returns r and min_operations(nums2) returns r2, then r = r2.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice I64) (h : ValidInput nums) (c : Int) (nums2 : Slice I64)
    (hlen : nums2.val.length = nums.val.length)
    (hshift : ∀ (i : Nat) (hi : i < nums2.val.length),
      (nums2.val.get ⟨i, hi⟩).val = (nums.val.get ⟨i, by omega⟩).val + c)
    (hrange2 : EntriesInRange nums2.val) (r r2 : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r)
    (hres2 : Aegis.MinOperations.min_operations nums2 = ok r2) : r.val = r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (c : Int) (nums2 : Slice I64)
    (hlen : nums2.val.length = nums.val.length)
    (hshift : ∀ (i : Nat) (hi : i < nums2.val.length),
      (nums2.val.get ⟨i, hi⟩).val = (nums.val.get ⟨i, by omega⟩).val + c)
    (hrange2 : EntriesInRange nums2.val) (r r2 : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r)
    (hres2 : Aegis.MinOperations.min_operations nums2 = ok r2), r.val = r2.val) := by
  sorry

/-- Let rev be the slice of length len(nums) defined by rev[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums). If min_operations(nums) returns r and min_operations(rev) returns rrev, then r = rrev.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice I64) (h : ValidInput nums) (rev : Slice I64)
    (hlen : rev.val.length = nums.val.length)
    (hrev : ∀ (i : Nat), i < nums.val.length →
      (rev.val[i]?).map (fun x => x.val) =
        (nums.val[nums.val.length - 1 - i]?).map (fun x => x.val))
    (r rrev : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r)
    (hresrev : Aegis.MinOperations.min_operations rev = ok rrev) : r.val = rrev.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (rev : Slice I64)
    (hlen : rev.val.length = nums.val.length)
    (hrev : ∀ (i : Nat), i < nums.val.length →
      (rev.val[i]?).map (fun x => x.val) =
        (nums.val[nums.val.length - 1 - i]?).map (fun x => x.val))
    (r rrev : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r)
    (hresrev : Aegis.MinOperations.min_operations rev = ok rrev), r.val = rrev.val) := by
  sorry

/-- Let comp be the slice obtained from nums by replacing each maximal contiguous block of equal elements by one occurrence of that common value; formally, if the maximal constant blocks of nums are B_0, ..., B_{m-1} in order, then len(comp) = m and comp[j] is the common value on B_j. If min_operations(nums) returns r and min_operations(comp) returns rc, then r = rc.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_9 (nums : Slice I64) (h : ValidInput nums) (comp : Slice I64)
    (hcomp : asInts comp = Compress (asInts nums))
    (r rc : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r)
    (hrescomp : Aegis.MinOperations.min_operations comp = ok rc) : r.val = rc.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (comp : Slice I64)
    (hcomp : asInts comp = Compress (asInts nums))
    (r rc : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r)
    (hrescomp : Aegis.MinOperations.min_operations comp = ok rc), r.val = rc.val) := by
  sorry

/-- For every integer m with 1 <= m and len(nums)*m <= 100000, let nums2 be the slice of length len(nums)*m defined by nums2[t*m + q] = nums[t] for every t with 0 <= t < len(nums) and every q with 0 <= q < m. If min_operations(nums) returns r and min_operations(nums2) returns r2, then r = r2.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice I64) (h : ValidInput nums) (m : Nat)
    (hm : 1 ≤ m) (_hm_len : nums.val.length * m ≤ 100000) (nums2 : Slice I64)
    (hlen : nums2.val.length = nums.val.length * m)
    (hrep : ∀ (t : Nat), t < nums.val.length → ∀ (q : Nat), q < m →
      (nums2.val[t * m + q]?).map (fun x => x.val) =
        (nums.val[t]?).map (fun x => x.val))
    (r r2 : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r)
    (hres2 : Aegis.MinOperations.min_operations nums2 = ok r2) : r.val = r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (m : Nat)
    (hm : 1 ≤ m) (_hm_len : nums.val.length * m ≤ 100000) (nums2 : Slice I64)
    (hlen : nums2.val.length = nums.val.length * m)
    (hrep : ∀ (t : Nat), t < nums.val.length → ∀ (q : Nat), q < m →
      (nums2.val[t * m + q]?).map (fun x => x.val) =
        (nums.val[t]?).map (fun x => x.val))
    (r r2 : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r)
    (hres2 : Aegis.MinOperations.min_operations nums2 = ok r2), r.val = r2.val) := by
  sorry

/-- Whenever the function returns a result r, r = D - 1, where D is the number of distinct values occurring in nums, that is, the cardinality of the set {nums[i] : 0 <= i < len(nums)}.
  Preconditions: len(nums) is between 1 and 100000 inclusive, for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000, and nums is non-decreasing: for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_11 (nums : Slice I64) (h : ValidInput nums)
    (hsorted : Nondecreasing nums.val) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r) :
    r.val = (DistinctCount nums.val : Int) - 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums)
    (hsorted : Nondecreasing nums.val) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r), r.val = (DistinctCount nums.val : Int) - 1) := by
  sorry

/-- Let r be the value returned by the function. There exists a sequence of exactly r operations that transforms nums into an array all of whose elements are equal, where each operation chooses an integer p with 1 <= p <= len(nums) and an integer k and adds k to each of the elements at positions 0 through p-1.
  Preconditions: len(nums) is between 1 and 100000 inclusive, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_12 (nums : Slice I64) (h : ValidInput nums) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r) :
    ∃ ops : List Op,
      ops.length = r.val.toNat ∧
        (∀ op ∈ ops, 1 ≤ op.p ∧ op.p ≤ nums.val.length) ∧
          IsConstant (ops.foldl applyOp (asInts nums)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (h : ValidInput nums) (r : I64)
    (hres : Aegis.MinOperations.min_operations nums = ok r), ∃ ops : List Op,
      ops.length = r.val.toNat ∧
        (∀ op ∈ ops, 1 ≤ op.p ∧ op.p ≤ nums.val.length) ∧
          IsConstant (ops.foldl applyOp (asInts nums))) := by
  sorry

end AegisSpec.MinOperations
