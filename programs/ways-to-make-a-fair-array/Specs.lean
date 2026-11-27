import Aegis.WaysToMakeFair.Code.Funs

/-!
# Specifications of `Aegis.WaysToMakeFair.ways_to_make_fair`

LeetCode problem `ways-to-make-a-fair-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.WaysToMakeFair

  namespace AegisSpec.WaysToMakeFair

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def removeAt (l : List ℤ) (i : ℕ) : List ℤ := l.eraseIdx i

  def sumEvenPos : List ℤ → ℤ
    | [] => 0
    | [x] => x
    | x :: _ :: xs => x + sumEvenPos xs

  def sumOddPos : List ℤ → ℤ
    | [] => 0
    | [_] => 0
    | _ :: y :: xs => y + sumOddPos xs

  def altSum (l : List ℤ) : ℤ := sumEvenPos l - sumOddPos l

  abbrev IsFairRemoval (nums : Slice Std.I64) (i : ℕ) : Prop :=
    sumEvenPos (removeAt (vals nums) i) = sumOddPos (removeAt (vals nums) i)

  def fairCount (nums : Slice Std.I64) : ℕ :=
    ((List.range nums.val.length).filter (fun i => decide (IsFairRemoval nums i))).length

  def ValidInput (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
      ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000

  /-- Let n = len(nums). For an index i with 0 <= i < n, let b_i be the array of length n-1 defined by b_i[j] = nums[j] for 0 <= j < i, and b_i[j] = nums[j+1] for i <= j < n-1. Call i fair-removable when the sum of b_i[j] over all even j with 0 <= j < n-1 equals the sum of b_i[j] over all odd j with 0 <= j < n-1, with the empty sum equal to 0. Then the function returns a result r and, as an integer, r equals the number of fair-removable indices i with 0 <= i < n.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_1 (nums : Slice Std.I64) (h : ValidInput nums) :
      ∃ r : Std.I64, ways_to_make_fair nums = ok r ∧ r.val = (fairCount nums : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∃ r : Std.I64, ways_to_make_fair nums = ok r ∧ r.val = (fairCount nums : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_2 (nums : Slice Std.I64) (h : ValidInput nums) :
      ∃ r : Std.I64, ways_to_make_fair nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∃ r : Std.I64, ways_to_make_fair nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, as an integer r satisfies 0 <= r <= len(nums).
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_3 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
      (hr : ways_to_make_fair nums = ok r) :
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
        (hr : ways_to_make_fair nums = ok r), 0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, as an integer r > 0 if and only if there exists an index i with 0 <= i < len(nums) such that removing nums[i] is fair: that is, for the array b_i of length len(nums)-1 with b_i[j] = nums[j] for 0 <= j < i and b_i[j] = nums[j+1] for i <= j < len(nums)-1, the sum of b_i[j] over even j equals the sum of b_i[j] over odd j, with empty sums equal to 0.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_4 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
      (hr : ways_to_make_fair nums = ok r) :
      0 < r.val ↔ ∃ i : ℕ, i < nums.val.length ∧ IsFairRemoval nums i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
        (hr : ways_to_make_fair nums = ok r), 0 < r.val ↔ ∃ i : ℕ, i < nums.val.length ∧ IsFairRemoval nums i) := by
    sorry

  /-- Whenever the function returns a result r, as an integer r = len(nums) if and only if for every index i with 0 <= i < len(nums), removing nums[i] is fair, where removing index i is fair when, in the array b_i of length len(nums)-1 with b_i[j] = nums[j] for 0 <= j < i and b_i[j] = nums[j+1] for i <= j < len(nums)-1, the sum over even j equals the sum over odd j, with empty sums equal to 0.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_5 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
      (hr : ways_to_make_fair nums = ok r) :
      r.val = (nums.val.length : ℤ) ↔
        ∀ i : ℕ, i < nums.val.length → IsFairRemoval nums i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
        (hr : ways_to_make_fair nums = ok r), r.val = (nums.val.length : ℤ) ↔
          ∀ i : ℕ, i < nums.val.length → IsFairRemoval nums i) := by
    sorry

  /-- Whenever the function returns a result r, if len(nums) = 1 then, as an integer, r = 1.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_6 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
      (hr : ways_to_make_fair nums = ok r) (hlen : nums.val.length = 1) :
      r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
        (hr : ways_to_make_fair nums = ok r) (hlen : nums.val.length = 1), r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, if len(nums) = 2 then, as an integer, r = 0.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_7 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
      (hr : ways_to_make_fair nums = ok r) (hlen : nums.val.length = 2) :
      r.val = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
        (hr : ways_to_make_fair nums = ok r) (hlen : nums.val.length = 2), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, as an integer r = 1 if and only if there is exactly one index i with 0 <= i < len(nums) such that removing nums[i] is fair, with fairness defined by the shifted array b_i: b_i[j] = nums[j] for 0 <= j < i, b_i[j] = nums[j+1] for i <= j < len(nums)-1, and the sum over even j equals the sum over odd j, empty sums being 0.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_8 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
      (hr : ways_to_make_fair nums = ok r) :
      r.val = 1 ↔ ∃! i : ℕ, i < nums.val.length ∧ IsFairRemoval nums i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
        (hr : ways_to_make_fair nums = ok r), r.val = 1 ↔ ∃! i : ℕ, i < nums.val.length ∧ IsFairRemoval nums i) := by
    sorry

  /-- Suppose len(nums) is odd. Let nums' be any slice with len(nums') = len(nums) and nums'[i] = nums[i] + c for every i with 0 <= i < len(nums), for some integer c, and suppose nums' also satisfies the preconditions. Let r be the result of the function on nums and r' be the result on nums'. Then r = r'.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_9 (nums nums' : Slice Std.I64) (c : ℤ)
      (h : ValidInput nums) (h' : ValidInput nums')
      (hodd : Odd nums.val.length)
      (hlen : nums'.val.length = nums.val.length)
      (hshift : ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < nums'.val.length),
        (nums'.val[i]'hi').val = (nums.val[i]'hi).val + c)
      (r r' : Std.I64)
      (hr : ways_to_make_fair nums = ok r) (hr' : ways_to_make_fair nums' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ)
        (h : ValidInput nums) (h' : ValidInput nums')
        (hodd : Odd nums.val.length)
        (hlen : nums'.val.length = nums.val.length)
        (hshift : ∀ (i : ℕ) (hi : i < nums.val.length) (hi' : i < nums'.val.length),
          (nums'.val[i]'hi').val = (nums.val[i]'hi).val + c)
        (r r' : Std.I64)
        (hr : ways_to_make_fair nums = ok r) (hr' : ways_to_make_fair nums' = ok r'), r.val = r'.val) := by
    sorry

  /-- Let T = sum_{k=0}^{len(nums)-1} (-1)^k * nums[k], where (-1)^k means 1 for even k and -1 for odd k. Whenever the function returns a result r, if r > 0 then there exists an index i with 0 <= i < len(nums) such that T - nums[i] is even.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
  theorem spec_10 (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
      (hr : ways_to_make_fair nums = ok r) (hpos : 0 < r.val) :
      ∃ (i : ℕ) (hi : i < nums.val.length),
        Even (altSum (vals nums) - (nums.val[i]'hi).val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums) (r : Std.I64)
        (hr : ways_to_make_fair nums = ok r) (hpos : 0 < r.val), ∃ (i : ℕ) (hi : i < nums.val.length),
          Even (altSum (vals nums) - (nums.val[i]'hi).val)) := by
    sorry

  end AegisSpec.WaysToMakeFair
