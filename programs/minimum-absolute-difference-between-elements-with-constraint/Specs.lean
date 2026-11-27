import Aegis.MinAbsoluteDifference.Code.Funs

/-!
# Specifications of `Aegis.MinAbsoluteDifference.min_absolute_difference`

LeetCode problem `minimum-absolute-difference-between-elements-with-constraint`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinAbsoluteDifference

  def nlen (nums : Slice Std.I64) : Nat := nums.val.length

  def nth (nums : Slice Std.I64) (i : Nat) : Int := (nums.val.getD i 0#i64).val

  def diff (nums : Slice Std.I64) (i j : Nat) : Int := |nth nums i - nth nums j|

  def gap (i j : Nat) : Int := |(i : Int) - (j : Int)|

  def feasible (nums : Slice Std.I64) (x : Int) (i j : Nat) : Prop :=
    i < nlen nums ∧ j < nlen nums ∧ gap i j ≥ x

  def maxElem (nums : Slice Std.I64) : Int :=
    match nums.val.map (fun v => v.val) with
    | [] => 0
    | v :: vs => vs.foldr max v

  def minElem (nums : Slice Std.I64) : Int :=
    match nums.val.map (fun v => v.val) with
    | [] => 0
    | v :: vs => vs.foldr min v

  def revSlice (nums : Slice Std.I64) : Slice Std.I64 where
    leng := nums.val.reverse.length
    list := Aeneas.Data.ListN.ListN.fromList nums.val.reverse
    bound := by
      have h1 : nums.val.reverse.length = nums.val.length := List.length_reverse
      have h2 : nums.val.length = nums.leng := Aeneas.Data.ListN.ListN_length nums.list
      rw [h1, h2]
      exact nums.bound

  structure Precond (nums : Slice Std.I64) (x : Std.I64) : Prop where

    n_pos : 1 ≤ nlen nums

    n_le : nlen nums ≤ 100000

    entry_pos : ∀ i, i < nlen nums → 1 ≤ nth nums i

    entry_le : ∀ i, i < nlen nums → nth nums i ≤ 1000000000

    x_nonneg : 0 ≤ x.val

    x_lt_n : x.val ≤ (nlen nums : Int) - 1

  /-- Let n = len(nums) and let D = { |nums[i] - nums[j]| : 0 <= i < n, 0 <= j < n, |i - j| >= x }. The function returns a result r such that r = min(D). Equivalently: (a) for every i, j with 0 <= i < n, 0 <= j < n, and |i - j| >= x, we have r <= |nums[i] - nums[j]|; and (b) there exist i, j with 0 <= i < n, 0 <= j < n, |i - j| >= x, and |nums[i] - nums[j]| = r.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_1 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∃ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r ∧
        (∀ i j, feasible nums x.val i j → r.val ≤ diff nums i j) ∧
        (∃ i j, feasible nums x.val i j ∧ diff nums i j = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∃ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r ∧
          (∀ i j, feasible nums x.val i j → r.val ≤ diff nums i j) ∧
          (∃ i j, feasible nums x.val i j ∧ diff nums i j = r.val)) := by
    sorry

  /-- For every nums and x satisfying the preconditions, the function returns a result r (it does not fail, overflow, or panic).
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_2 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∃ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∃ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r) := by
    sorry

  /-- The returned value r satisfies r >= 0.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_3 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r → 0 ≤ r.val) := by
    sorry

  /-- Let n = len(nums), M = max_{0 <= i < n} nums[i], and m = min_{0 <= i < n} nums[i]. Then r <= M - m.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_4 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
        r.val ≤ maxElem nums - minElem nums := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
          r.val ≤ maxElem nums - minElem nums) := by
    sorry

  /-- The returned value r is 0 if and only if x = 0 or there exist indices i, j with 0 <= i < n, 0 <= j < n, |i - j| >= x, and nums[i] = nums[j].
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_5 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
        (r.val = 0 ↔ x.val = 0 ∨ ∃ i j, feasible nums x.val i j ∧ nth nums i = nth nums j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
          (r.val = 0 ↔ x.val = 0 ∨ ∃ i j, feasible nums x.val i j ∧ nth nums i = nth nums j)) := by
    sorry

  /-- Let n = len(nums). If x = n - 1, then r = |nums[0] - nums[n - 1]|.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_6 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
        x.val = (nlen nums : Int) - 1 →
          r.val = |nth nums 0 - nth nums (nlen nums - 1)| := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
          x.val = (nlen nums : Int) - 1 →
            r.val = |nth nums 0 - nth nums (nlen nums - 1)|) := by
    sorry

  /-- There exist indices i, j with 0 <= i < n, 0 <= j < n, |i - j| >= x, and r = |nums[i] - nums[j]|.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_7 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
        ∃ i j, feasible nums x.val i j ∧ r.val = diff nums i j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
          ∃ i j, feasible nums x.val i j ∧ r.val = diff nums i j) := by
    sorry

  /-- For every i, j with 0 <= i < n, 0 <= j < n, and |i - j| >= x, we have r <= |nums[i] - nums[j]|.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_8 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
        ∀ i j, feasible nums x.val i j → r.val ≤ diff nums i j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
          ∀ i j, feasible nums x.val i j → r.val ≤ diff nums i j) := by
    sorry

  /-- If x >= 1 and nums[i] != nums[j] for every pair (i, j) with 0 <= i < n, 0 <= j < n, and i != j, then r >= 1.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_9 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
        1 ≤ x.val →
          (∀ i j, i < nlen nums → j < nlen nums → i ≠ j → nth nums i ≠ nth nums j) →
            1 ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
          1 ≤ x.val →
            (∀ i j, i < nlen nums → j < nlen nums → i ≠ j → nth nums i ≠ nth nums j) →
              1 ≤ r.val) := by
    sorry

  /-- r <= 1000000000 - 1 = 999999999.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_10 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
        r.val ≤ 999999999 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
          r.val ≤ 999999999) := by
    sorry

  /-- Let n = len(nums). If x >= 1, then r = min{ |nums[i] - nums[j]| : 0 <= i < j < n and j - i >= x }.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_11 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
        1 ≤ x.val →
          (∀ i j, i < j → j < nlen nums → gap i j ≥ x.val → r.val ≤ diff nums i j) ∧
            (∃ i j, i < j ∧ j < nlen nums ∧ gap i j ≥ x.val ∧ r.val = diff nums i j) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∀ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r →
          1 ≤ x.val →
            (∀ i j, i < j → j < nlen nums → gap i j ≥ x.val → r.val ≤ diff nums i j) ∧
              (∃ i j, i < j ∧ j < nlen nums ∧ gap i j ≥ x.val ∧ r.val = diff nums i j)) := by
    sorry

  /-- Let n = len(nums) and let rev be the array of length n defined by rev[i] = nums[n - 1 - i] for 0 <= i < n. Then the minimum absolute difference for rev with the same x equals r.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; 0 <= x <= n - 1. -/
  theorem spec_12 (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x) :
      ∃ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r ∧
        Aegis.MinAbsoluteDifference.min_absolute_difference (revSlice nums) x = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (x : Std.I64) (h : Precond nums x), ∃ r, Aegis.MinAbsoluteDifference.min_absolute_difference nums x = ok r ∧
          Aegis.MinAbsoluteDifference.min_absolute_difference (revSlice nums) x = ok r) := by
    sorry

  end AegisSpec.MinAbsoluteDifference
