import Aegis.LargestDivisibleSubset.Code.Funs

/-!
# Specifications of `Aegis.LargestDivisibleSubset.largest_divisible_subset`

LeetCode problem `largest-divisible-subset`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LargestDivisibleSubset

  def sliceVals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def vecVals (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

  def Occurs (x : Int) (l : List Int) : Prop := x ∈ l

  def PairwiseNe (l : List Int) : Prop :=
    ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i ≠ j → l[i] ≠ l[j]

  theorem pairwiseNe_iff_nodup (l : List Int) : PairwiseNe l ↔ l.Nodup := by
    constructor
    · intro h
      rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
      intro i j hi hj hij hEq
      exact h i j hi hj (Nat.ne_of_lt hij) hEq
    · intro h i j hi hj hij hEq
      exact hij (List.Nodup.getElem_inj h |>.mp hEq)

  def PairwiseDiv (l : List Int) : Prop :=
    ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i ≠ j → l[i] % l[j] = 0 ∨ l[j] % l[i] = 0

  def PairwiseNonDiv (l : List Int) : Prop :=
    ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i ≠ j →
      l[i] % l[j] ≠ 0 ∧ l[j] % l[i] ≠ 0

  def IsValidDivSubset (nums : List Int) (S : List Int) : Prop :=
    (∀ x, Occurs x S → Occurs x nums) ∧ PairwiseNe S ∧ PairwiseDiv S

  def IsMinOf (l : List Int) (m : Int) : Prop := Occurs m l ∧ ∀ x, Occurs x l → m ≤ x

  def IsMaxOf (l : List Int) (M : Int) : Prop := Occurs M l ∧ ∀ x, Occurs x l → x ≤ M

  def Precond (nums : Slice Std.I64) : Prop :=
    1 ≤ (sliceVals nums).length ∧
      (sliceVals nums).length ≤ 1000 ∧
      (∀ (i : Nat) (hi : i < (sliceVals nums).length),
        1 ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ 2000000000) ∧
      PairwiseNe (sliceVals nums)

  /-- Whenever the function returns a result r, call a list S a valid divisible subset of nums if (i) every element of S occurs in nums, (ii) all elements of S are pairwise distinct, and (iii) for all distinct indices a,b of S, S[a] % S[b] = 0 or S[b] % S[a] = 0. Then r itself is a valid divisible subset of nums, and for every valid divisible subset S of nums, len(S) <= len(r).
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and for every i,j with 0 <= i < n, 0 <= j < n, if i != j then nums[i] != nums[j]. -/
  theorem spec_1 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r) :
      IsValidDivSubset (sliceVals nums) (vecVals r) ∧
        ∀ S : List Int, IsValidDivSubset (sliceVals nums) S → S.length ≤ (vecVals r).length := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r), IsValidDivSubset (sliceVals nums) (vecVals r) ∧
          ∀ S : List Int, IsValidDivSubset (sliceVals nums) S → S.length ≤ (vecVals r).length) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail due to arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and for every i,j with 0 <= i < n, 0 <= j < n, if i != j then nums[i] != nums[j]. -/
  theorem spec_2 (nums : Slice Std.I64) (hpre : Precond nums) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : Precond nums), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), there exists j with 0 <= j < len(nums) such that r[i] = nums[j].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_3 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r) :
      ∀ (i : Nat) (hi : i < (vecVals r).length),
        ∃ (j : Nat) (hj : j < (sliceVals nums).length), (vecVals r)[i] = (sliceVals nums)[j] := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r), ∀ (i : Nat) (hi : i < (vecVals r).length),
          ∃ (j : Nat) (hj : j < (sliceVals nums).length), (vecVals r)[i] = (sliceVals nums)[j]) := by
    sorry

  /-- Whenever the function returns a result r, for every i,j with 0 <= i < len(r), 0 <= j < len(r), if i != j then r[i] != r[j].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_4 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r) :
      PairwiseNe (vecVals r) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r), PairwiseNe (vecVals r)) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= len(r) <= len(nums) <= 1000.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_5 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r) :
      0 ≤ (vecVals r).length ∧ (vecVals r).length ≤ (sliceVals nums).length ∧
        (sliceVals nums).length ≤ 1000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r), 0 ≤ (vecVals r).length ∧ (vecVals r).length ≤ (sliceVals nums).length ∧
          (sliceVals nums).length ≤ 1000) := by
    sorry

  /-- Whenever the function returns a result r, for every i,j with 0 <= i < len(r), 0 <= j < len(r), if i != j then r[i] % r[j] = 0 or r[j] % r[i] = 0.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_6 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r) :
      PairwiseDiv (vecVals r) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r), PairwiseDiv (vecVals r)) := by
    sorry

  /-- Whenever the function returns a result r, for every list S of integers such that every element of S occurs in nums, all elements of S are pairwise distinct, and for all distinct indices a,b of S one has S[a] % S[b] = 0 or S[b] % S[a] = 0, it follows that len(S) <= len(r).
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_7 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r) :
      ∀ S : List Int, IsValidDivSubset (sliceVals nums) S → S.length ≤ (vecVals r).length := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r), ∀ S : List Int, IsValidDivSubset (sliceVals nums) S → S.length ≤ (vecVals r).length) := by
    sorry

  /-- Whenever the function returns a result r, len(r) >= 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_8 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r) :
      1 ≤ (vecVals r).length := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r), 1 ≤ (vecVals r).length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 1 <= r[i] <= 2_000_000_000.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_9 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r) :
      ∀ (i : Nat) (hi : i < (vecVals r).length),
        1 ≤ (vecVals r)[i] ∧ (vecVals r)[i] ≤ 2000000000 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r), ∀ (i : Nat) (hi : i < (vecVals r).length),
          1 ≤ (vecVals r)[i] ∧ (vecVals r)[i] ≤ 2000000000) := by
    sorry

  /-- Whenever the function returns a result r, if for every i,j with 0 <= i < n, 0 <= j < n, i != j, one has nums[i] % nums[j] = 0 or nums[j] % nums[i] = 0, then len(r) = len(nums) and for every j with 0 <= j < len(nums) there exists i with 0 <= i < len(r) such that r[i] = nums[j].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_10 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
      (hchain : PairwiseDiv (sliceVals nums)) :
      (vecVals r).length = (sliceVals nums).length ∧
        ∀ (j : Nat) (hj : j < (sliceVals nums).length),
          ∃ (i : Nat) (hi : i < (vecVals r).length), (vecVals r)[i] = (sliceVals nums)[j] := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
        (hchain : PairwiseDiv (sliceVals nums)), (vecVals r).length = (sliceVals nums).length ∧
          ∀ (j : Nat) (hj : j < (sliceVals nums).length),
            ∃ (i : Nat) (hi : i < (vecVals r).length), (vecVals r)[i] = (sliceVals nums)[j]) := by
    sorry

  /-- Whenever the function returns a result r, if for every i,j with 0 <= i < n, 0 <= j < n, i != j, one has nums[i] % nums[j] != 0 and nums[j] % nums[i] != 0, then len(r) = 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_11 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
      (hanti : PairwiseNonDiv (sliceVals nums)) :
      (vecVals r).length = 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
        (hanti : PairwiseNonDiv (sliceVals nums)), (vecVals r).length = 1) := by
    sorry

  /-- Whenever the function returns a result r and len(r) > 0, if m is the minimum of the values r[0],...,r[len(r)-1], then for every i with 0 <= i < len(r), r[i] % m = 0.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_12 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
      (hlen : 0 < (vecVals r).length) (m : Int) (hm : IsMinOf (vecVals r) m) :
      ∀ (i : Nat) (hi : i < (vecVals r).length), (vecVals r)[i] % m = 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
        (hlen : 0 < (vecVals r).length) (m : Int) (hm : IsMinOf (vecVals r) m), ∀ (i : Nat) (hi : i < (vecVals r).length), (vecVals r)[i] % m = 0) := by
    sorry

  /-- Whenever the function returns a result r and len(r) > 0, if M is the maximum of the values r[0],...,r[len(r)-1], then for every i with 0 <= i < len(r), M % r[i] = 0.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_13 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
      (hlen : 0 < (vecVals r).length) (M : Int) (hM : IsMaxOf (vecVals r) M) :
      ∀ (i : Nat) (hi : i < (vecVals r).length), M % (vecVals r)[i] = 0 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
        (hlen : 0 < (vecVals r).length) (M : Int) (hM : IsMaxOf (vecVals r) M), ∀ (i : Nat) (hi : i < (vecVals r).length), M % (vecVals r)[i] = 0) := by
    sorry

  /-- Whenever the function returns a result r and len(r) > 0, for every x that occurs in nums but does not occur in r, there exists i with 0 <= i < len(r) such that r[i] % x != 0 and x % r[i] != 0.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_14 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
      (hlen : 0 < (vecVals r).length) :
      ∀ x : Int, Occurs x (sliceVals nums) → ¬ Occurs x (vecVals r) →
        ∃ (i : Nat) (hi : i < (vecVals r).length),
          (vecVals r)[i] % x ≠ 0 ∧ x % (vecVals r)[i] ≠ 0 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
        (hlen : 0 < (vecVals r).length), ∀ x : Int, Occurs x (sliceVals nums) → ¬ Occurs x (vecVals r) →
          ∃ (i : Nat) (hi : i < (vecVals r).length),
            (vecVals r)[i] % x ≠ 0 ∧ x % (vecVals r)[i] ≠ 0) := by
    sorry

  /-- Whenever the function returns a result r, if there exists j with 0 <= j < len(nums) such that nums[j] = 1, then there exists i with 0 <= i < len(r) such that r[i] = 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 2_000_000_000; and nums is duplicate-free. -/
  theorem spec_15 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (hpre : Precond nums)
      (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
      (h1 : ∃ (j : Nat) (hj : j < (sliceVals nums).length), (sliceVals nums)[j] = 1) :
      ∃ (i : Nat) (hi : i < (vecVals r).length), (vecVals r)[i] = 1 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (hpre : Precond nums)
        (hr : Aegis.LargestDivisibleSubset.largest_divisible_subset nums = ok r)
        (h1 : ∃ (j : Nat) (hj : j < (sliceVals nums).length), (sliceVals nums)[j] = 1), ∃ (i : Nat) (hi : i < (vecVals r).length), (vecVals r)[i] = 1) := by
    sorry

  end AegisSpec.LargestDivisibleSubset
