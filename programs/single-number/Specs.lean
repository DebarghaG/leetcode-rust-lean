import Aegis.SingleNumber.Code.Funs

/-!
# Specifications of `Aegis.SingleNumber.single_number`

LeetCode problem `single-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SingleNumber

  def count (nums : Slice Std.I64) (x : Std.I64) : Nat :=
    nums.val.countP (fun y => decide (y = x))

  def minVal (nums : Slice Std.I64) : Int :=
    match nums.val with
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => min acc y.val) x.val

  def maxVal (nums : Slice Std.I64) : Int :=
    match nums.val with
    | [] => 0
    | x :: xs => xs.foldl (fun acc y => max acc y.val) x.val

  def xorAll (nums : Slice Std.I64) : Std.I64 :=
    nums.val.foldl (fun acc y => acc ^^^ y) 0#i64

  /-- The function returns a result r, and r is the unique value v with count(nums, v) = 1; equivalently, count(nums, r) = 1 and for every value w with count(nums, w) > 0 and w != r, count(nums, w) = 2.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∃ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r ∧
        count nums r = 1 ∧
        (∀ w : Std.I64, count nums w > 0 → w ≠ r → count nums w = 2) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∃ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r ∧
          count nums r = 1 ∧
          (∀ w : Std.I64, count nums w > 0 → w ≠ r → count nums w = 2)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular, it does not fail, overflow, access nums out of bounds, or panic.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∃ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∃ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(nums) such that r = nums[i].
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
        ∃ (i : Nat) (hi : i < nums.val.length), r = nums.val[i] := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
          ∃ (i : Nat) (hi : i < nums.val.length), r = nums.val[i]) := by
    sorry

  /-- Whenever the function returns a result r, count(nums, r) = 1.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r → count nums r = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r → count nums r = 1) := by
    sorry

  /-- Whenever the function returns a result r, for every value w with count(nums, w) > 0 and w != r, count(nums, w) = 2.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
        ∀ w : Std.I64, count nums w > 0 → w ≠ r → count nums w = 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
          ∀ w : Std.I64, count nums w > 0 → w ≠ r → count nums w = 2) := by
    sorry

  /-- Whenever the function returns a result r, there exists exactly one index k with 0 <= k < len(nums) such that nums[k] = r; that is, nums[k] = r and for every j with 0 <= j < len(nums) and j != k, nums[j] != r.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
        ∃ (k : Nat) (hk : k < nums.val.length),
          nums.val[k] = r ∧
          ∀ (j : Nat) (hj : j < nums.val.length), j ≠ k → nums.val[j] ≠ r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
          ∃ (k : Nat) (hk : k < nums.val.length),
            nums.val[k] = r ∧
            ∀ (j : Nat) (hj : j < nums.val.length), j ≠ k → nums.val[j] ≠ r) := by
    sorry

  /-- Whenever the function returns a result r, min(nums) <= r <= max(nums), where min(nums) is the smallest nums[i] and max(nums) is the largest nums[i] over 0 <= i < len(nums).
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
        minVal nums ≤ r.val ∧ r.val ≤ maxVal nums := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
          minVal nums ≤ r.val ∧ r.val ≤ maxVal nums) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(nums) and nums[i] != r, there exists exactly one index j with 0 <= j < len(nums), j != i, and nums[j] = nums[i].
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length), nums.val[i] ≠ r →
          ∃ (j : Nat) (hj : j < nums.val.length),
            j ≠ i ∧ nums.val[j] = nums.val[i] ∧
            (∀ (j' : Nat) (hj' : j' < nums.val.length),
              j' ≠ i → nums.val[j'] = nums.val[i] → j' = j) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
          ∀ (i : Nat) (hi : i < nums.val.length), nums.val[i] ≠ r →
            ∃ (j : Nat) (hj : j < nums.val.length),
              j ≠ i ∧ nums.val[j] = nums.val[i] ∧
              (∀ (j' : Nat) (hj' : j' < nums.val.length),
                j' ≠ i → nums.val[j'] = nums.val[i] → j' = j)) := by
    sorry

  /-- Whenever the function returns a result r, for every two distinct indices i and j with 0 <= i < len(nums), 0 <= j < len(nums), and i != j, if nums[i] = nums[j] then nums[i] != r.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
        ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
          i ≠ j → nums.val[i] = nums.val[j] → nums.val[i] ≠ r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
          ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
            i ≠ j → nums.val[i] = nums.val[j] → nums.val[i] ≠ r) := by
    sorry

  /-- For every slice nums2 of i64 such that len(nums2) = len(nums) and count(nums2, x) = count(nums, x) for every value x, if the function returns a result r on nums and a result r2 on nums2, then r2 = r.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∀ nums2 : Slice Std.I64,
        nums2.val.length = nums.val.length →
        (∀ x : Std.I64, count nums2 x = count nums x) →
        ∀ (r r2 : Std.I64),
          Aegis.SingleNumber.single_number nums = ok r →
          Aegis.SingleNumber.single_number nums2 = ok r2 → r2 = r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∀ nums2 : Slice Std.I64,
          nums2.val.length = nums.val.length →
          (∀ x : Std.I64, count nums2 x = count nums x) →
          ∀ (r r2 : Std.I64),
            Aegis.SingleNumber.single_number nums = ok r →
            Aegis.SingleNumber.single_number nums2 = ok r2 → r2 = r) := by
    sorry

  /-- Whenever the function returns a result r, for every value w with count(nums, w) > 0, count(nums, w) is odd if and only if w = r.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
        ∀ w : Std.I64, count nums w > 0 → (Odd (count nums w) ↔ w = r) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∀ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r →
          ∀ w : Std.I64, count nums w > 0 → (Odd (count nums w) ↔ w = r)) := by
    sorry

  /-- The function returns a result r, and r = nums[0] ⊕ nums[1] ⊕ ... ⊕ nums[len(nums)-1], where ⊕ is 64-bit bitwise XOR.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; for every index i with 0 <= i < len(nums), -30000 <= nums[i] <= 30000; and there exists a value v such that count(nums, v) = 1 and, for every value w with count(nums, w) > 0 and w != v, count(nums, w) = 2, where count(nums, x) is the number of indices i with 0 <= i < len(nums) such that nums[i] = x. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
        -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
      (hcount : ∃ v : Std.I64, count nums v = 1 ∧
        ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2) :
      ∃ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r ∧ r = xorAll nums := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ (i : Nat) (hi : i < nums.val.length),
          -30000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 30000)
        (hcount : ∃ v : Std.I64, count nums v = 1 ∧
          ∀ w : Std.I64, count nums w > 0 → w ≠ v → count nums w = 2), ∃ r : Std.I64, Aegis.SingleNumber.single_number nums = ok r ∧ r = xorAll nums) := by
    sorry

  end AegisSpec.SingleNumber
