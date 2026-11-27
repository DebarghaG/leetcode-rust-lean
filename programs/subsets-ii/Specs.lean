import Aegis.SubsetsWithDup.Code.Funs

/-!
# Specifications of `Aegis.SubsetsWithDup.subsets_with_dup`

LeetCode problem `subsets-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SubsetsWithDup

open Classical

def cnt (a : List Std.I64) (x : ℤ) : ℕ :=
  (a.map (fun v => v.val)).countP (fun y => decide (y = x))

def distinctVals (a : List Std.I64) : List ℤ :=
  (a.map (fun v => v.val)).dedup

def numSubMultisets (a : List Std.I64) : ℕ :=
  ((distinctVals a).map (fun u => cnt a u + 1)).prod

def numSubMultisetsExcept (a : List Std.I64) (v : ℤ) : ℕ :=
  (((distinctVals a).filter (fun u => decide (u ≠ v))).map (fun u => cnt a u + 1)).prod

def entry (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : ℕ) : List Std.I64 :=
  ((r.val[i]?).map (fun e => e.val)).getD []

noncomputable def cntIdx (n : ℕ) (p : ℕ → Prop) : ℕ :=
  letI := Classical.propDecidable
  ((List.range n).filter (fun i => decide (p i))).length

def totalCnt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (v : ℤ) : ℕ :=
  ((List.range r.val.length).map (fun i => cnt (entry r i) v)).sum

/-- Whenever the function returns a result r, for every finite vector s of 64-bit integers, the number of indices i with 0 <= i < len(r) and cnt(r[i], x) = cnt(s, x) for every integer x is exactly 1 if cnt(s, x) <= cnt(nums, x) for every integer x, and is exactly 0 otherwise. Here cnt(a, x) is the number of positions j in a with a[j] = x. Thus the entries of r, identified up to permutation of their elements, are precisely all distinct sub-multisets of nums, each occurring once, and the outer order of entries in r is arbitrary.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∀ s : List Std.I64,
      cntIdx r.val.length (fun i => ∀ x : ℤ, cnt (entry r i) x = cnt s x) =
        if (∀ x : ℤ, cnt s x ≤ cnt nums.val x) then 1 else 0 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∀ s : List Std.I64,
      cntIdx r.val.length (fun i => ∀ x : ℤ, cnt (entry r i) x = cnt s x) =
        if (∀ x : ℤ, cnt s x ≤ cnt nums.val x) then 1 else 0) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.SubsetsWithDup.subsets_with_dup nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = product over v in D of (cnt(nums, v) + 1), where D is the finite set of distinct integers occurring in nums and cnt(nums, v) is the number of indices j with nums[j] = v. Equivalently, len(r) is the number of distinct sub-multisets of nums.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    r.val.length = numSubMultisets nums.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), r.val.length = numSubMultisets nums.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r) and every integer x, cnt(r[i], x) <= cnt(nums, x), where cnt(a, x) is the number of occurrences of x in a. In particular, every returned vector is a sub-multiset of nums and contains no value more times than nums does.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∀ i : ℕ, i < r.val.length → ∀ x : ℤ, cnt (entry r i) x ≤ cnt nums.val x := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∀ i : ℕ, i < r.val.length → ∀ x : ℤ, cnt (entry r i) x ≤ cnt nums.val x) := by
  sorry

/-- Whenever the function returns a result r, for all i and j with 0 <= i < len(r) and 0 <= j < len(r), if cnt(r[i], x) = cnt(r[j], x) for every integer x, then i = j. Thus no two entries of r represent the same subset, even after reordering their elements.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∀ i j : ℕ, i < r.val.length → j < r.val.length →
      (∀ x : ℤ, cnt (entry r i) x = cnt (entry r j) x) → i = j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∀ i j : ℕ, i < r.val.length → j < r.val.length →
      (∀ x : ℤ, cnt (entry r i) x = cnt (entry r j) x) → i = j) := by
  sorry

/-- Whenever the function returns a result r, for every finite vector s of 64-bit integers satisfying cnt(s, x) <= cnt(nums, x) for every integer x, there exists i with 0 <= i < len(r) such that cnt(r[i], x) = cnt(s, x) for every integer x. Thus every sub-multiset of nums is represented among the entries of r.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∀ s : List Std.I64, (∀ x : ℤ, cnt s x ≤ cnt nums.val x) →
      ∃ i : ℕ, i < r.val.length ∧ ∀ x : ℤ, cnt (entry r i) x = cnt s x := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∀ s : List Std.I64, (∀ x : ℤ, cnt s x ≤ cnt nums.val x) →
      ∃ i : ℕ, i < r.val.length ∧ ∀ x : ℤ, cnt (entry r i) x = cnt s x) := by
  sorry

/-- Whenever the function returns a result r, 1 <= len(r) <= 2^len(nums).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    1 ≤ r.val.length ∧ r.val.length ≤ 2 ^ nums.val.length := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), 1 ≤ r.val.length ∧ r.val.length ≤ 2 ^ nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 0 <= len(r[i]) <= len(nums).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∀ i : ℕ, i < r.val.length → (entry r i).length ≤ nums.val.length := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∀ i : ℕ, i < r.val.length → (entry r i).length ≤ nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, there is exactly one index i with 0 <= i < len(r) such that len(r[i]) = 0, namely the empty subset.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∃! i : ℕ, i < r.val.length ∧ (entry r i).length = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∃! i : ℕ, i < r.val.length ∧ (entry r i).length = 0) := by
  sorry

/-- Whenever the function returns a result r, there is exactly one index i with 0 <= i < len(r) such that cnt(r[i], x) = cnt(nums, x) for every integer x, namely the subset containing the whole multiset nums.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_10 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∃! i : ℕ, i < r.val.length ∧ ∀ x : ℤ, cnt (entry r i) x = cnt nums.val x := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∃! i : ℕ, i < r.val.length ∧ ∀ x : ℤ, cnt (entry r i) x = cnt nums.val x) := by
  sorry

/-- Whenever the function returns a result r, for every integer v with cnt(nums, v) > 0, there is exactly one index i with 0 <= i < len(r) such that len(r[i]) = 1 and r[i][0] = v.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_11 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∀ v : ℤ, 0 < cnt nums.val v →
      ∃! i : ℕ, i < r.val.length ∧ ∃ w : Std.I64, w.val = v ∧ entry r i = [w] := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∀ v : ℤ, 0 < cnt nums.val v →
      ∃! i : ℕ, i < r.val.length ∧ ∃ w : Std.I64, w.val = v ∧ entry r i = [w]) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 0 <= k <= len(nums), there exists an index i with 0 <= i < len(r) such that len(r[i]) = k.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_12 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∀ k : ℕ, k ≤ nums.val.length →
      ∃ i : ℕ, i < r.val.length ∧ (entry r i).length = k := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∀ k : ℕ, k ≤ nums.val.length →
      ∃ i : ℕ, i < r.val.length ∧ (entry r i).length = k) := by
  sorry

/-- Whenever the function returns a result r, for every integer v and every integer k with 0 <= k <= cnt(nums, v), the number of indices i with 0 <= i < len(r) and cnt(r[i], v) = k is exactly the product over u in D with u != v of (cnt(nums, u) + 1), where D is the set of distinct integers occurring in nums. An empty product is 1. In particular, for each value v present in nums and each possible multiplicity k of v, there is one returned subset for every choice of multiplicities of the other values.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_13 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∀ v : ℤ, ∀ k : ℕ, k ≤ cnt nums.val v →
      cntIdx r.val.length (fun i => cnt (entry r i) v = k) =
        numSubMultisetsExcept nums.val v := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∀ v : ℤ, ∀ k : ℕ, k ≤ cnt nums.val v →
      cntIdx r.val.length (fun i => cnt (entry r i) v = k) =
        numSubMultisetsExcept nums.val v) := by
  sorry

/-- Whenever the function returns a result r for nums and a result r' for nums', for every i with 0 <= i < len(r) there exists j with 0 <= j < len(r') such that cnt(r[i], x) = cnt(r'[j], x) for every integer x; and for every j with 0 <= j < len(r') there exists i with 0 <= i < len(r) satisfying the same equality. Consequently len(r) = len(r').
  Preconditions: nums and nums' are slices of 64-bit integers, each with length between 1 and 10 and all entries in [-10, 10], and cnt(nums', x) = cnt(nums, x) for every integer x, so nums' is a permutation of nums. -/
theorem spec_14 (nums nums' : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (h_len_ge' : 1 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 10)
    (h_bnd' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      -10 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10)
    (h_counts : ∀ x : ℤ, cnt nums'.val x = cnt nums.val x)
    (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r)
    (hr' : Aegis.SubsetsWithDup.subsets_with_dup nums' = ok r') :
    (∀ i : ℕ, i < r.val.length →
        ∃ j : ℕ, j < r'.val.length ∧ ∀ x : ℤ, cnt (entry r i) x = cnt (entry r' j) x) ∧
      (∀ j : ℕ, j < r'.val.length →
        ∃ i : ℕ, i < r.val.length ∧ ∀ x : ℤ, cnt (entry r i) x = cnt (entry r' j) x) ∧
      r.val.length = r'.val.length := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (h_len_ge' : 1 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 10)
    (h_bnd' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      -10 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10)
    (h_counts : ∀ x : ℤ, cnt nums'.val x = cnt nums.val x)
    (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r)
    (hr' : Aegis.SubsetsWithDup.subsets_with_dup nums' = ok r'), (∀ i : ℕ, i < r.val.length →
        ∃ j : ℕ, j < r'.val.length ∧ ∀ x : ℤ, cnt (entry r i) x = cnt (entry r' j) x) ∧
      (∀ j : ℕ, j < r'.val.length →
        ∃ i : ℕ, i < r.val.length ∧ ∀ x : ℤ, cnt (entry r i) x = cnt (entry r' j) x) ∧
      r.val.length = r'.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the sum over i with 0 <= i < len(r) of cnt(r[i], v) equals (c * (c + 1) / 2) * product over u in D with u != v of (cnt(nums, u) + 1), where c = cnt(nums, v) and D is the set of distinct integers occurring in nums. Here the product is over all u in D except v, and an empty product is 1. In particular, if v is not in nums, this sum is 0.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 10 and -10 <= nums[i] <= 10 for every i with 0 <= i < len(nums). -/
theorem spec_15 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r) :
    ∀ v : ℤ,
      totalCnt r v =
        (cnt nums.val v * (cnt nums.val v + 1) / 2) * numSubMultisetsExcept nums.val v := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10)
    (h_bnd : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.SubsetsWithDup.subsets_with_dup nums = ok r), ∀ v : ℤ,
      totalCnt r v =
        (cnt nums.val v * (cnt nums.val v + 1) / 2) * numSubMultisetsExcept nums.val v) := by
  sorry

end AegisSpec.SubsetsWithDup
