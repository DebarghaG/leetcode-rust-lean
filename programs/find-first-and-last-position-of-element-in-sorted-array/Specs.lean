import Aegis.SearchRange.Code.Funs

/-!
# Specifications of `Aegis.SearchRange.search_range`

LeetCode problem `find-first-and-last-position-of-element-in-sorted-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SearchRange

  open Aegis.SearchRange

  def elemAt (nums : Aeneas.Std.Slice Aeneas.Std.I64) (i : Nat) : Int :=
    (nums.val[i]!).val

  def resEntry (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64) (i : Nat) : Int :=
    (r.val[i]!).val

  def elemAtRes (nums : Aeneas.Std.Slice Aeneas.Std.I64)
      (r : Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64) (i : Nat) : Int :=
    elemAt nums (resEntry r i).toNat

  def len (nums : Aeneas.Std.Slice Aeneas.Std.I64) : Nat :=
    nums.val.length

  def Occurs (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64) : Prop :=
    ∃ k, k < len nums ∧ elemAt nums k = target.val

  def Nondecreasing (nums : Aeneas.Std.Slice Aeneas.Std.I64) : Prop :=
    ∀ i j, i ≤ j → j < len nums → elemAt nums i ≤ elemAt nums j

  def LenBound (nums : Aeneas.Std.Slice Aeneas.Std.I64) : Prop :=
    len nums ≤ 100000

  def IntervalOK (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64) : Prop :=
    (∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000) ∧
      (-1000000000 ≤ target.val ∧ target.val ≤ 1000000000)

  def countLt (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64) : Nat :=
    nums.val.countP (fun x => decide (x.val < target.val))

  def countLe (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64) : Nat :=
    nums.val.countP (fun x => decide (x.val ≤ target.val))

  def countEq (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64) : Nat :=
    nums.val.countP (fun x => decide (x.val = target.val))

  /-- Let n = len(nums). The function returns a result r and: if there exists k with 0 ≤ k < n and nums[k] = target, then len(r) = 2, 0 ≤ r[0] < n, 0 ≤ r[1] < n, r[0] ≤ r[1], nums[r[0]] = target, nums[r[1]] = target, for every i with 0 ≤ i < r[0] we have nums[i] ≠ target, and for every i with r[1] < i < n we have nums[i] ≠ target; otherwise, i.e. if no such k exists, len(r) = 2, r[0] = -1, and r[1] = -1.
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_1 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∃ r, search_range nums target = ok r ∧
        ((Occurs nums target →
            r.val.length = 2 ∧
              (0 : Int) ≤ resEntry r 0 ∧ resEntry r 0 < (len nums : Int) ∧
              (0 : Int) ≤ resEntry r 1 ∧ resEntry r 1 < (len nums : Int) ∧
              resEntry r 0 ≤ resEntry r 1 ∧
              elemAtRes nums r 0 = target.val ∧
              elemAtRes nums r 1 = target.val ∧
              (∀ i, i < (resEntry r 0).toNat → elemAt nums i ≠ target.val) ∧
              (∀ i, (resEntry r 1).toNat < i → i < len nums → elemAt nums i ≠ target.val)) ∧
          (¬ Occurs nums target →
            r.val.length = 2 ∧ resEntry r 0 = -1 ∧ resEntry r 1 = -1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∃ r, search_range nums target = ok r ∧
          ((Occurs nums target →
              r.val.length = 2 ∧
                (0 : Int) ≤ resEntry r 0 ∧ resEntry r 0 < (len nums : Int) ∧
                (0 : Int) ≤ resEntry r 1 ∧ resEntry r 1 < (len nums : Int) ∧
                resEntry r 0 ≤ resEntry r 1 ∧
                elemAtRes nums r 0 = target.val ∧
                elemAtRes nums r 1 = target.val ∧
                (∀ i, i < (resEntry r 0).toNat → elemAt nums i ≠ target.val) ∧
                (∀ i, (resEntry r 1).toNat < i → i < len nums → elemAt nums i ≠ target.val)) ∧
            (¬ Occurs nums target →
              r.val.length = 2 ∧ resEntry r 0 = -1 ∧ resEntry r 1 = -1))) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail.
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_2 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∃ r, search_range nums target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∃ r, search_range nums target = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2.
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_3 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → r.val.length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → r.val.length = 2) := by
    sorry

  /-- Whenever the function returns r and there is no index k with 0 ≤ k < len(nums) and nums[k] = target, then len(r) = 2, r[0] = -1, and r[1] = -1.
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_4 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → ¬ Occurs nums target →
        r.val.length = 2 ∧ resEntry r 0 = -1 ∧ resEntry r 1 = -1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → ¬ Occurs nums target →
          r.val.length = 2 ∧ resEntry r 0 = -1 ∧ resEntry r 1 = -1) := by
    sorry

  /-- Whenever the function returns r and there exists k with 0 ≤ k < len(nums) and nums[k] = target, then 0 ≤ r[0] < len(nums), nums[r[0]] = target, and for every i with 0 ≤ i < r[0], nums[i] ≠ target.
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_5 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → Occurs nums target →
        (0 : Int) ≤ resEntry r 0 ∧ resEntry r 0 < (len nums : Int) ∧
          elemAtRes nums r 0 = target.val ∧
          (∀ i, i < (resEntry r 0).toNat → elemAt nums i ≠ target.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → Occurs nums target →
          (0 : Int) ≤ resEntry r 0 ∧ resEntry r 0 < (len nums : Int) ∧
            elemAtRes nums r 0 = target.val ∧
            (∀ i, i < (resEntry r 0).toNat → elemAt nums i ≠ target.val)) := by
    sorry

  /-- Whenever the function returns r and there exists k with 0 ≤ k < len(nums) and nums[k] = target, then 0 ≤ r[1] < len(nums), nums[r[1]] = target, and for every i with r[1] < i < len(nums), nums[i] ≠ target.
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_6 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → Occurs nums target →
        (0 : Int) ≤ resEntry r 1 ∧ resEntry r 1 < (len nums : Int) ∧
          elemAtRes nums r 1 = target.val ∧
          (∀ i, (resEntry r 1).toNat < i → i < len nums → elemAt nums i ≠ target.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → Occurs nums target →
          (0 : Int) ≤ resEntry r 1 ∧ resEntry r 1 < (len nums : Int) ∧
            elemAtRes nums r 1 = target.val ∧
            (∀ i, (resEntry r 1).toNat < i → i < len nums → elemAt nums i ≠ target.val)) := by
    sorry

  /-- Whenever the function returns r and there exists k with 0 ≤ k < len(nums) and nums[k] = target, then both reported positions are valid indices: 0 ≤ r[0] < len(nums) and 0 ≤ r[1] < len(nums).
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_7 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → Occurs nums target →
        (0 : Int) ≤ resEntry r 0 ∧ resEntry r 0 < (len nums : Int) ∧
          (0 : Int) ≤ resEntry r 1 ∧ resEntry r 1 < (len nums : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → Occurs nums target →
          (0 : Int) ≤ resEntry r 0 ∧ resEntry r 0 < (len nums : Int) ∧
            (0 : Int) ≤ resEntry r 1 ∧ resEntry r 1 < (len nums : Int)) := by
    sorry

  /-- Whenever the function returns a result r, its two entries satisfy r[0] ≤ r[1].
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_8 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → resEntry r 0 ≤ resEntry r 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → resEntry r 0 ≤ resEntry r 1) := by
    sorry

  /-- Whenever the function returns r and there exists k with 0 ≤ k < len(nums) and nums[k] = target, then for every i with 0 ≤ i < len(nums), nums[i] = target if and only if r[0] ≤ i ≤ r[1].
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_9 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → Occurs nums target →
        ∀ i, i < len nums →
          (elemAt nums i = target.val ↔ resEntry r 0 ≤ (i : Int) ∧ (i : Int) ≤ resEntry r 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → Occurs nums target →
          ∀ i, i < len nums →
            (elemAt nums i = target.val ↔ resEntry r 0 ≤ (i : Int) ∧ (i : Int) ≤ resEntry r 1)) := by
    sorry

  /-- Whenever the function returns r and there exists k with 0 ≤ k < len(nums) and nums[k] = target, then every index before r[0] stores a value strictly less than target, and every index after r[1] stores a value strictly greater than target: for every i with 0 ≤ i < r[0], nums[i] < target, and for every i with r[1] < i < len(nums), target < nums[i].
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_10 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → Occurs nums target →
        (∀ i, i < (resEntry r 0).toNat → elemAt nums i < target.val) ∧
          (∀ i, (resEntry r 1).toNat < i → i < len nums → target.val < elemAt nums i) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → Occurs nums target →
          (∀ i, i < (resEntry r 0).toNat → elemAt nums i < target.val) ∧
            (∀ i, (resEntry r 1).toNat < i → i < len nums → target.val < elemAt nums i)) := by
    sorry

  /-- Whenever the function returns r and there exists k with 0 ≤ k < len(nums) and nums[k] = target, then the integer value r[0] equals the number of indices i with 0 ≤ i < len(nums) and nums[i] < target.
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_11 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → Occurs nums target →
        resEntry r 0 = Int.ofNat (countLt nums target) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → Occurs nums target →
          resEntry r 0 = Int.ofNat (countLt nums target)) := by
    sorry

  /-- Whenever the function returns r and there exists k with 0 ≤ k < len(nums) and nums[k] = target, then r[1] + 1 equals the number of indices i with 0 ≤ i < len(nums) and nums[i] ≤ target.
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_12 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → Occurs nums target →
        resEntry r 1 + 1 = Int.ofNat (countLe nums target) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → Occurs nums target →
          resEntry r 1 + 1 = Int.ofNat (countLe nums target)) := by
    sorry

  /-- Whenever the function returns r and there exists k with 0 ≤ k < len(nums) and nums[k] = target, then r[0] = r[1] if and only if exactly one index i with 0 ≤ i < len(nums) satisfies nums[i] = target.
    Preconditions: 0 ≤ len(nums) ≤ 100000; nums is non-decreasing, i.e. for every i and j with 0 ≤ i ≤ j < len(nums), nums[i] ≤ nums[j]; and every element of nums and target lies in [-1000000000, 1000000000]. -/
  theorem spec_13 (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
      (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target) :
      ∀ r, search_range nums target = ok r → Occurs nums target →
        (resEntry r 0 = resEntry r 1 ↔ countEq nums target = 1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (target : Aeneas.Std.I64)
        (hlen : LenBound nums) (hsorted : Nondecreasing nums) (hbounds : IntervalOK nums target), ∀ r, search_range nums target = ok r → Occurs nums target →
          (resEntry r 0 = resEntry r 1 ↔ countEq nums target = 1)) := by
    sorry

  end AegisSpec.SearchRange
