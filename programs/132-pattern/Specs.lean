import Aegis.Find132pattern.Code.Funs

/-!
# Specifications of `Aegis.Find132pattern.find132pattern`

LeetCode problem `132-pattern`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Find132pattern

  /-- The function returns a result r and, for that r, r = true if and only if there exist indices i, j, k such that 0 <= i < j < k < len(nums) and nums[i] < nums[k] < nums[j]. Equivalently, r = false if and only if no such triple of indices exists.
    Preconditions: len(nums) >= 1 and len(nums) <= 200000 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 200000)
      (h_bnd : ∀ i : Nat, i < nums.val.length →
        -1000000000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∃ r : Bool, Aegis.Find132pattern.find132pattern nums = ok r ∧
        (r = true ↔ ∃ i j k : Nat,
          i < j ∧ j < k ∧ k < nums.val.length ∧
            (nums.val[i]!).val < (nums.val[k]!).val ∧
            (nums.val[k]!).val < (nums.val[j]!).val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 200000)
        (h_bnd : ∀ i : Nat, i < nums.val.length →
          -1000000000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∃ r : Bool, Aegis.Find132pattern.find132pattern nums = ok r ∧
          (r = true ↔ ∃ i j k : Nat,
            i < j ∧ j < k ∧ k < nums.val.length ∧
              (nums.val[i]!).val < (nums.val[k]!).val ∧
              (nums.val[k]!).val < (nums.val[j]!).val)) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, arithmetic overflow, or out-of-bounds access) for any input satisfying the preconditions.
    Preconditions: len(nums) >= 1 and len(nums) <= 200000 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 200000)
      (h_bnd : ∀ i : Nat, i < nums.val.length →
        -1000000000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∃ r : Bool, Aegis.Find132pattern.find132pattern nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 200000)
        (h_bnd : ∀ i : Nat, i < nums.val.length →
          -1000000000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∃ r : Bool, Aegis.Find132pattern.find132pattern nums = ok r) := by
    sorry

  /-- Whenever find132pattern nums returns a result r and find132pattern ys returns a result s, r = s.
    Preconditions: len(nums) = len(ys) = n with 1 <= n <= 200000; for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9 and -10^9 <= ys[i] <= 10^9; and for every i, j with 0 <= i < n and 0 <= j < n, nums[i] < nums[j] if and only if ys[i] < ys[j]. -/
  theorem spec_3 (nums ys : Slice Std.I64) (n : Nat)
      (h_len_nums : nums.val.length = n)
      (h_len_ys : ys.val.length = n)
      (h_n_ge : 1 ≤ n)
      (h_n_le : n ≤ 200000)
      (h_bnd_nums : ∀ i : Nat, i < n →
        -1000000000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000)
      (h_bnd_ys : ∀ i : Nat, i < n →
        -1000000000 ≤ (ys.val[i]!).val ∧ (ys.val[i]!).val ≤ 1000000000)
      (h_order : ∀ i j : Nat, i < n → j < n →
        ((nums.val[i]!).val < (nums.val[j]!).val ↔
          (ys.val[i]!).val < (ys.val[j]!).val)) :
      ∀ r s : Bool, Aegis.Find132pattern.find132pattern nums = ok r →
        Aegis.Find132pattern.find132pattern ys = ok s → r = s := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums ys : Slice Std.I64) (n : Nat)
        (h_len_nums : nums.val.length = n)
        (h_len_ys : ys.val.length = n)
        (h_n_ge : 1 ≤ n)
        (h_n_le : n ≤ 200000)
        (h_bnd_nums : ∀ i : Nat, i < n →
          -1000000000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000)
        (h_bnd_ys : ∀ i : Nat, i < n →
          -1000000000 ≤ (ys.val[i]!).val ∧ (ys.val[i]!).val ≤ 1000000000)
        (h_order : ∀ i j : Nat, i < n → j < n →
          ((nums.val[i]!).val < (nums.val[j]!).val ↔
            (ys.val[i]!).val < (ys.val[j]!).val)), ∀ r s : Bool, Aegis.Find132pattern.find132pattern nums = ok r →
          Aegis.Find132pattern.find132pattern ys = ok s → r = s) := by
    sorry

  /-- Whenever the function returns a result r with r = true, there exist indices i, j, k such that 0 <= i < j < k < len(nums), nums[i] < nums[k] < nums[j], and nums[j] >= nums[t] for every t with i < t <= k.
    Preconditions: len(nums) >= 1 and len(nums) <= 200000 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 200000)
      (h_bnd : ∀ i : Nat, i < nums.val.length →
        -1000000000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∀ r : Bool, Aegis.Find132pattern.find132pattern nums = ok r → r = true →
        ∃ i j k : Nat,
          i < j ∧ j < k ∧ k < nums.val.length ∧
            (nums.val[i]!).val < (nums.val[k]!).val ∧
            (nums.val[k]!).val < (nums.val[j]!).val ∧
            (∀ t : Nat, i < t → t ≤ k → (nums.val[t]!).val ≤ (nums.val[j]!).val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 200000)
        (h_bnd : ∀ i : Nat, i < nums.val.length →
          -1000000000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∀ r : Bool, Aegis.Find132pattern.find132pattern nums = ok r → r = true →
          ∃ i j k : Nat,
            i < j ∧ j < k ∧ k < nums.val.length ∧
              (nums.val[i]!).val < (nums.val[k]!).val ∧
              (nums.val[k]!).val < (nums.val[j]!).val ∧
              (∀ t : Nat, i < t → t ≤ k → (nums.val[t]!).val ≤ (nums.val[j]!).val)) := by
    sorry

  /-- Whenever the function returns a result r with r = true, there exist indices i, j, k such that 0 <= i < j < k < len(nums), nums[i] < nums[k] < nums[j], and nums[i] <= nums[t] for every integer t with 0 <= t < j.
    Preconditions: len(nums) >= 1 and len(nums) <= 200000 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 200000)
      (h_bnd : ∀ i : Nat, i < nums.val.length →
        -1000000000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∀ r : Bool, Aegis.Find132pattern.find132pattern nums = ok r → r = true →
        ∃ i j k : Nat,
          i < j ∧ j < k ∧ k < nums.val.length ∧
            (nums.val[i]!).val < (nums.val[k]!).val ∧
            (nums.val[k]!).val < (nums.val[j]!).val ∧
            (∀ t : Nat, t < j → (nums.val[i]!).val ≤ (nums.val[t]!).val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 200000)
        (h_bnd : ∀ i : Nat, i < nums.val.length →
          -1000000000 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∀ r : Bool, Aegis.Find132pattern.find132pattern nums = ok r → r = true →
          ∃ i j k : Nat,
            i < j ∧ j < k ∧ k < nums.val.length ∧
              (nums.val[i]!).val < (nums.val[k]!).val ∧
              (nums.val[k]!).val < (nums.val[j]!).val ∧
              (∀ t : Nat, t < j → (nums.val[i]!).val ≤ (nums.val[t]!).val)) := by
    sorry

  end AegisSpec.Find132pattern
