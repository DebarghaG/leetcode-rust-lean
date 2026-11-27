import Aegis.CanBeIncreasing.Code.Funs

/-!
# Specifications of `Aegis.CanBeIncreasing.can_be_increasing`

LeetCode problem `remove-one-element-to-make-the-array-strictly-increasing`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanBeIncreasing

  open Aeneas.Std.Result

  def StrictlyIncreasing : List Aeneas.Std.I64 → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => a.val < b.val ∧ StrictlyIncreasing (b :: rest)

  def deleteAt (l : List Aeneas.Std.I64) (j : Nat) : List Aeneas.Std.I64 :=
    l.take j ++ l.drop (j + 1)

  /-- The function returns a result r (it does not fail), and r = true if and only if there exists an index j with 0 <= j < len(nums) such that deleting the element at position j from nums gives a strictly increasing sequence. Deleting position j from a sequence of length n gives the sequence of length n-1 whose k-th element, for 0 <= k < n-1, is nums[k] when k < j and nums[k+1] when k >= j; this deleted sequence is strictly increasing when for every k with 0 <= k < len(nums)-2, its k-th element is less than its (k+1)-th element. If no such j exists, r = false.
    Preconditions: 2 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 1000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∃ (r : Bool), Aegis.CanBeIncreasing.can_be_increasing nums = ok r ∧
        (r = true ↔ ∃ (j : Nat) (_hj : j < nums.val.length),
          StrictlyIncreasing (deleteAt nums.val j)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 1000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∃ (r : Bool), Aegis.CanBeIncreasing.can_be_increasing nums = ok r ∧
          (r = true ↔ ∃ (j : Nat) (_hj : j < nums.val.length),
            StrictlyIncreasing (deleteAt nums.val j))) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: 2 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 1000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∃ (r : Bool), Aegis.CanBeIncreasing.can_be_increasing nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 1000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∃ (r : Bool), Aegis.CanBeIncreasing.can_be_increasing nums = ok r) := by
    sorry

  /-- The function returns a result r and r = true.
    Preconditions: len(nums) = 2, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : nums.val.length = 2)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∃ (r : Bool), Aegis.CanBeIncreasing.can_be_increasing nums = ok r ∧ r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length = 2)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∃ (r : Bool), Aegis.CanBeIncreasing.can_be_increasing nums = ok r ∧ r = true) := by
    sorry

  /-- Whenever the function returns a result r with r = true, there is at most one index i with 0 <= i < len(nums)-1 such that nums[i] >= nums[i+1].
    Preconditions: 2 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 1000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (r : Bool) (hres : Aegis.CanBeIncreasing.can_be_increasing nums = ok r)
      (hr : r = true) :
      ∀ (i j : Nat) (hi : i < nums.val.length - 1) (hj : j < nums.val.length - 1),
        (nums.val[i + 1]'(by omega)).val ≤ (nums.val[i]'(by omega)).val →
        (nums.val[j + 1]'(by omega)).val ≤ (nums.val[j]'(by omega)).val →
        i = j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 1000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (r : Bool) (hres : Aegis.CanBeIncreasing.can_be_increasing nums = ok r)
        (hr : r = true), ∀ (i j : Nat) (hi : i < nums.val.length - 1) (hj : j < nums.val.length - 1),
          (nums.val[i + 1]'(by omega)).val ≤ (nums.val[i]'(by omega)).val →
          (nums.val[j + 1]'(by omega)).val ≤ (nums.val[j]'(by omega)).val →
          i = j) := by
    sorry

  /-- Whenever the function returns a result r with r = true, there exists an index j with 0 <= j < len(nums) such that: (a) for every k with 0 <= k and k+1 < j, nums[k] < nums[k+1]; (b) for every k with j+1 <= k and k+1 < len(nums), nums[k] < nums[k+1]; and (c) if 0 < j and j+1 < len(nums), then nums[j-1] < nums[j+1].
    Preconditions: 2 <= len(nums) <= 1000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 1000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (r : Bool) (hres : Aegis.CanBeIncreasing.can_be_increasing nums = ok r)
      (hr : r = true) :
      ∃ (j : Nat) (_hj : j < nums.val.length),

        (∀ (k : Nat) (_hk : k + 1 < j),
          (nums.val[k]'(by omega)).val < (nums.val[k + 1]'(by omega)).val) ∧

        (∀ (k : Nat) (_hk : j + 1 ≤ k) (_hk' : k + 1 < nums.val.length),
          (nums.val[k]'(by omega)).val < (nums.val[k + 1]'(by omega)).val) ∧

        (∀ (hj0 : 0 < j) (hj1 : j + 1 < nums.val.length),
          (nums.val[j - 1]'(by omega)).val < (nums.val[j + 1]'hj1).val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 1000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (r : Bool) (hres : Aegis.CanBeIncreasing.can_be_increasing nums = ok r)
        (hr : r = true), ∃ (j : Nat) (_hj : j < nums.val.length),

          (∀ (k : Nat) (_hk : k + 1 < j),
            (nums.val[k]'(by omega)).val < (nums.val[k + 1]'(by omega)).val) ∧

          (∀ (k : Nat) (_hk : j + 1 ≤ k) (_hk' : k + 1 < nums.val.length),
            (nums.val[k]'(by omega)).val < (nums.val[k + 1]'(by omega)).val) ∧

          (∀ (hj0 : 0 < j) (hj1 : j + 1 < nums.val.length),
            (nums.val[j - 1]'(by omega)).val < (nums.val[j + 1]'hj1).val)) := by
    sorry

  /-- The function returns a result r and r = true if and only if at least one of nums[0] < nums[1], nums[0] < nums[2], or nums[1] < nums[2] holds.
    Preconditions: len(nums) = 3, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : nums.val.length = 3)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∃ (r : Bool), Aegis.CanBeIncreasing.can_be_increasing nums = ok r ∧
        (r = true ↔
          ((nums.val[0]'(by omega)).val < (nums.val[1]'(by omega)).val ∨
           (nums.val[0]'(by omega)).val < (nums.val[2]'(by omega)).val ∨
           (nums.val[1]'(by omega)).val < (nums.val[2]'(by omega)).val)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length = 3)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∃ (r : Bool), Aegis.CanBeIncreasing.can_be_increasing nums = ok r ∧
          (r = true ↔
            ((nums.val[0]'(by omega)).val < (nums.val[1]'(by omega)).val ∨
             (nums.val[0]'(by omega)).val < (nums.val[2]'(by omega)).val ∨
             (nums.val[1]'(by omega)).val < (nums.val[2]'(by omega)).val))) := by
    sorry

  /-- The function returns a result r and r = false.
    Preconditions: len(nums) >= 3, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000, and there exists an integer c such that nums[i] = c for every i with 0 <= i < len(nums). -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 3 ≤ nums.val.length)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (c : ℤ)
      (hconst : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = c) :
      ∃ (r : Bool), Aegis.CanBeIncreasing.can_be_increasing nums = ok r ∧ r = false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 3 ≤ nums.val.length)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (c : ℤ)
        (hconst : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val = c), ∃ (r : Bool), Aegis.CanBeIncreasing.can_be_increasing nums = ok r ∧ r = false) := by
    sorry

  /-- Let r be the result of the function on nums and r' the result of the function on nums'. Then both calls return results and r = r'.
    Preconditions: 2 <= len(nums) <= 1000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000, and nums' is any slice with len(nums') = len(nums), 1 <= nums'[i] <= 1000 for every 0 <= i < len(nums'), and for every i,k with 0 <= i < len(nums) and 0 <= k < len(nums), nums[i] < nums[k] if and only if nums'[i] < nums'[k]. -/
  theorem spec_8 (nums nums' : Slice Std.I64)
      (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 1000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hlen' : nums'.val.length = nums.val.length)
      (hbounds' : ∀ (i : Nat) (hi : i < nums'.val.length),
        1 ≤ (nums'.val[i]'hi).val ∧ (nums'.val[i]'hi).val ≤ 1000)
      (hord : ∀ (i k : Nat) (hi : i < nums.val.length) (hk : k < nums.val.length),
        ((nums.val[i]'hi).val < (nums.val[k]'hk).val ↔
         (nums'.val[i]'(by omega)).val < (nums'.val[k]'(by omega)).val)) :
      ∃ (r r' : Bool),
        Aegis.CanBeIncreasing.can_be_increasing nums = ok r ∧
        Aegis.CanBeIncreasing.can_be_increasing nums' = ok r' ∧ r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 1000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hlen' : nums'.val.length = nums.val.length)
        (hbounds' : ∀ (i : Nat) (hi : i < nums'.val.length),
          1 ≤ (nums'.val[i]'hi).val ∧ (nums'.val[i]'hi).val ≤ 1000)
        (hord : ∀ (i k : Nat) (hi : i < nums.val.length) (hk : k < nums.val.length),
          ((nums.val[i]'hi).val < (nums.val[k]'hk).val ↔
           (nums'.val[i]'(by omega)).val < (nums'.val[k]'(by omega)).val)), ∃ (r r' : Bool),
          Aegis.CanBeIncreasing.can_be_increasing nums = ok r ∧
          Aegis.CanBeIncreasing.can_be_increasing nums' = ok r' ∧ r = r') := by
    sorry

  /-- Whenever the function returns a result r with r = true on input nums, it returns a result r' with r' = true on input nums'.
    Preconditions: 2 <= len(nums) <= 999, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; let x be an integer with 1 <= x <= 1000 and x < nums[i] for every i with 0 <= i < len(nums); let nums' be the slice with len(nums') = len(nums)+1, nums'[0] = x, and nums'[i+1] = nums[i] for every 0 <= i < len(nums). -/
  theorem spec_9 (nums nums' : Slice Std.I64)
      (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 999)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (x : ℤ) (hx_lower : 1 ≤ x) (hx_upper : x ≤ 1000)
      (hx_lt : ∀ (i : Nat) (hi : i < nums.val.length), x < (nums.val[i]'hi).val)
      (hlen' : nums'.val.length = nums.val.length + 1)
      (hhead : (nums'.val[0]'(by omega)).val = x)
      (htail : ∀ (i : Nat) (hi : i < nums.val.length),
        (nums'.val[i + 1]'(by omega)).val = (nums.val[i]'hi).val)
      (r : Bool) (hres : Aegis.CanBeIncreasing.can_be_increasing nums = ok r)
      (hr : r = true) :
      ∃ (r' : Bool), Aegis.CanBeIncreasing.can_be_increasing nums' = ok r' ∧ r' = true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen_lower : 2 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 999)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (x : ℤ) (hx_lower : 1 ≤ x) (hx_upper : x ≤ 1000)
        (hx_lt : ∀ (i : Nat) (hi : i < nums.val.length), x < (nums.val[i]'hi).val)
        (hlen' : nums'.val.length = nums.val.length + 1)
        (hhead : (nums'.val[0]'(by omega)).val = x)
        (htail : ∀ (i : Nat) (hi : i < nums.val.length),
          (nums'.val[i + 1]'(by omega)).val = (nums.val[i]'hi).val)
        (r : Bool) (hres : Aegis.CanBeIncreasing.can_be_increasing nums = ok r)
        (hr : r = true), ∃ (r' : Bool), Aegis.CanBeIncreasing.can_be_increasing nums' = ok r' ∧ r' = true) := by
    sorry

  end AegisSpec.CanBeIncreasing
