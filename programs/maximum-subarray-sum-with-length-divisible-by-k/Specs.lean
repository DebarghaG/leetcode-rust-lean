import Aegis.MaxSubarraySum.Code.Funs

/-!
# Specifications of `Aegis.MaxSubarraySum.max_subarray_sum`

LeetCode problem `maximum-subarray-sum-with-length-divisible-by-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxSubarraySum

  open Aegis.MaxSubarraySum

  def sumRange (nums : List Std.I64) (i j : ℕ) : ℤ :=
    ((nums.drop i).take (j - i)).foldl (fun acc x => acc + x.val) 0

  def blockSums (nums : Slice Std.I64) (k : ℤ) : Set ℤ :=
    {s | ∃ i j : ℕ, i < j ∧ j ≤ nums.val.length ∧ k ∣ ((j : ℤ) - (i : ℤ)) ∧
        sumRange nums.val i j = s}

  def windowSums (nums : Slice Std.I64) (m : ℕ) : Set ℤ :=
    {s | ∃ i : ℕ, i + m ≤ nums.val.length ∧ sumRange nums.val i (i + m) = s}

  def IsMaxOf (S : Set ℤ) (m : ℤ) : Prop := (∀ x ∈ S, x ≤ m) ∧ (∃ x ∈ S, x = m)

  def negSum (nums : Slice Std.I64) : ℤ :=
    nums.val.foldl (fun acc x => if x.val < 0 then acc + x.val else acc) 0

  def posSum (nums : Slice Std.I64) : ℤ :=
    nums.val.foldl (fun acc x => if 0 < x.val then acc + x.val else acc) 0

  def listNOfList {α : Type} : (l : List α) → Aeneas.Data.ListN.ListN α l.length
    | [] => .nil
    | a :: l => .cons a (listNOfList l)

  def revSlice (nums : Slice Std.I64) : Slice Std.I64 :=
    { leng := nums.val.reverse.length
      list := listNOfList nums.val.reverse
      bound := by rw [List.length_reverse]; exact Slice.length_ineq nums }

  theorem listNOfList_toList {α : Type} (l : List α) : (listNOfList l).toList = l := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      show (Aeneas.Data.ListN.ListN.cons a (listNOfList l)).toList = a :: l
      exact congrArg (List.cons a) ih

  theorem revSlice_val (nums : Slice Std.I64) : (revSlice nums).val = nums.val.reverse := by
    simp [revSlice, Slice.val, listNOfList_toList]

  theorem revSlice_get (nums : Slice Std.I64) (i : ℕ) (hi : i < nums.val.length) :
      (revSlice nums).val[i]? = nums.val[nums.val.length - 1 - i]? := by
    rw [revSlice_val]
    exact List.getElem?_reverse hi

  /-- The function returns a result r, and r equals the maximum of the set of all integers of the form the sum of nums[t] over all t with i <= t < j, where 0 <= i < j <= len(nums) and j - i is a positive multiple of k (equivalently, k divides j - i).
    Preconditions: len(nums) >= 1; len(nums) <= 2 * 10^5; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
      (h_k_pos : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9) :
      ∃ r : Std.I64, max_subarray_sum nums k = ok r ∧
        IsMaxOf (blockSums nums k.val) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
        (h_k_pos : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9), ∃ r : Std.I64, max_subarray_sum nums k = ok r ∧
          IsMaxOf (blockSums nums k.val) r.val) := by
    sorry

  /-- The function returns a result (it does not fail, overflow, panic, or get stuck) for every input satisfying the preconditions.
    Preconditions: len(nums) >= 1; len(nums) <= 2 * 10^5; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
      (h_k_pos : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9) :
      ∃ r : Std.I64, max_subarray_sum nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
        (h_k_pos : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9), ∃ r : Std.I64, max_subarray_sum nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j <= len(nums) and k dividing j - i, the sum of nums[t] over i <= t < j is at most r.
    Preconditions: len(nums) >= 1; len(nums) <= 2 * 10^5; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
      (h_k_pos : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_subarray_sum nums k = ok r →
        ∀ (i j : ℕ), i < j → j ≤ nums.val.length → k.val ∣ ((j : ℤ) - (i : ℤ)) →
          sumRange nums.val i j ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
        (h_k_pos : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9), ∀ r : Std.I64, max_subarray_sum nums k = ok r →
          ∀ (i j : ℕ), i < j → j ≤ nums.val.length → k.val ∣ ((j : ℤ) - (i : ℤ)) →
            sumRange nums.val i j ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i and j with 0 <= i < j <= len(nums) and k dividing j - i such that r equals the sum of nums[t] over i <= t < j.
    Preconditions: len(nums) >= 1; len(nums) <= 2 * 10^5; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
      (h_k_pos : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_subarray_sum nums k = ok r →
        ∃ (i j : ℕ), i < j ∧ j ≤ nums.val.length ∧ k.val ∣ ((j : ℤ) - (i : ℤ)) ∧
          r.val = sumRange nums.val i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
        (h_k_pos : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9), ∀ r : Std.I64, max_subarray_sum nums k = ok r →
          ∃ (i j : ℕ), i < j ∧ j ≤ nums.val.length ∧ k.val ∣ ((j : ℤ) - (i : ℤ)) ∧
            r.val = sumRange nums.val i j) := by
    sorry

  /-- Whenever the function returns a result r, let N be the sum of all nums[i] with nums[i] < 0 (and N = 0 if there are no such entries), and let P be the sum of all nums[i] with nums[i] > 0 (and P = 0 if there are no such entries). Then N <= r <= P.
    Preconditions: len(nums) >= 1; len(nums) <= 2 * 10^5; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
      (h_k_pos : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_subarray_sum nums k = ok r →
        negSum nums ≤ r.val ∧ r.val ≤ posSum nums := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
        (h_k_pos : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9), ∀ r : Std.I64, max_subarray_sum nums k = ok r →
          negSum nums ≤ r.val ∧ r.val ≤ posSum nums) := by
    sorry

  /-- Whenever the function returns a result r, -2 * 10^14 <= r <= 2 * 10^14.
    Preconditions: len(nums) >= 1; len(nums) <= 2 * 10^5; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
      (h_k_pos : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9) :
      ∀ r : Std.I64, max_subarray_sum nums k = ok r →
        -(2 * 10 ^ 14 : ℤ) ≤ r.val ∧ r.val ≤ 2 * 10 ^ 14 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
        (h_k_pos : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9), ∀ r : Std.I64, max_subarray_sum nums k = ok r →
          -(2 * 10 ^ 14 : ℤ) ≤ r.val ∧ r.val ≤ 2 * 10 ^ 14) := by
    sorry

  /-- If every nums[i] >= 0, let m = (len(nums) / k) * k, where / denotes integer division. Whenever the function returns a result r, r equals the maximum, over i with 0 <= i <= len(nums) - m, of the sum of nums[t] over i <= t < i + m.
    Preconditions: len(nums) >= 1; len(nums) <= 2 * 10^5; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9 and nums[i] >= 0. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
      (h_k_pos : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9)
      (h_nonneg : ∀ (i : ℕ) (hi : i < nums.val.length), 0 ≤ nums.val[i].val) :
      ∀ r : Std.I64, max_subarray_sum nums k = ok r →
        IsMaxOf (windowSums nums ((nums.val.length / k.val.toNat) * k.val.toNat)) r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
        (h_k_pos : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9)
        (h_nonneg : ∀ (i : ℕ) (hi : i < nums.val.length), 0 ≤ nums.val[i].val), ∀ r : Std.I64, max_subarray_sum nums k = ok r →
          IsMaxOf (windowSums nums ((nums.val.length / k.val.toNat) * k.val.toNat)) r.val) := by
    sorry

  /-- If every nums[i] <= 0, whenever the function returns a result r, r equals the maximum, over i with 0 <= i <= len(nums) - k, of the sum of nums[t] over i <= t < i + k.
    Preconditions: len(nums) >= 1; len(nums) <= 2 * 10^5; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9 and nums[i] <= 0. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
      (h_k_pos : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9)
      (h_nonpos : ∀ (i : ℕ) (hi : i < nums.val.length), nums.val[i].val ≤ 0) :
      ∀ r : Std.I64, max_subarray_sum nums k = ok r →
        IsMaxOf (windowSums nums k.val.toNat) r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
        (h_k_pos : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9)
        (h_nonpos : ∀ (i : ℕ) (hi : i < nums.val.length), nums.val[i].val ≤ 0), ∀ r : Std.I64, max_subarray_sum nums k = ok r →
          IsMaxOf (windowSums nums k.val.toNat) r.val) := by
    sorry

  /-- Let rev(nums) be the array with rev(nums)[i] = nums[len(nums) - 1 - i] for 0 <= i < len(nums). Whenever the function called on nums and k returns r and the function called on rev(nums) and k returns s, we have r = s.
    Preconditions: len(nums) >= 1; len(nums) <= 2 * 10^5; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
      (h_k_pos : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9) :
      ∀ r s : Std.I64, max_subarray_sum nums k = ok r →
        max_subarray_sum (revSlice nums) k = ok s → r.val = s.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 2 * 10 ^ 5)
        (h_k_pos : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_bounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -(10 ^ 9 : ℤ) ≤ nums.val[i].val ∧ nums.val[i].val ≤ 10 ^ 9), ∀ r s : Std.I64, max_subarray_sum nums k = ok r →
          max_subarray_sum (revSlice nums) k = ok s → r.val = s.val) := by
    sorry

  /-- Whenever the function called on a and k returns r and the function called on b and k returns s, we have r <= s.
    Preconditions: n >= 1; n <= 2 * 10^5; 1 <= k <= n; a and b are arrays of length n; for every i with 0 <= i < n, -10^9 <= a[i] <= 10^9 and -10^9 <= b[i] <= 10^9 and a[i] <= b[i]. -/
  theorem spec_10 (a b : Slice Std.I64) (k : Std.I64) (n : ℕ)
      (h_n_pos : 1 ≤ n)
      (h_n_le : n ≤ 2 * 10 ^ 5)
      (h_a_len : a.val.length = n)
      (h_b_len : b.val.length = n)
      (h_k_pos : 1 ≤ k.val)
      (h_k_le : k.val ≤ (n : ℤ))
      (h_a_bounds : ∀ (i : ℕ) (hi : i < n),
        -(10 ^ 9 : ℤ) ≤ (a.val.get ⟨i, by omega⟩).val ∧ (a.val.get ⟨i, by omega⟩).val ≤ 10 ^ 9)
      (h_b_bounds : ∀ (i : ℕ) (hi : i < n),
        -(10 ^ 9 : ℤ) ≤ (b.val.get ⟨i, by omega⟩).val ∧ (b.val.get ⟨i, by omega⟩).val ≤ 10 ^ 9)
      (h_le : ∀ (i : ℕ) (hi : i < n),
        (a.val.get ⟨i, by omega⟩).val ≤ (b.val.get ⟨i, by omega⟩).val) :
      ∀ r s : Std.I64, max_subarray_sum a k = ok r →
        max_subarray_sum b k = ok s → r.val ≤ s.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (a b : Slice Std.I64) (k : Std.I64) (n : ℕ)
        (h_n_pos : 1 ≤ n)
        (h_n_le : n ≤ 2 * 10 ^ 5)
        (h_a_len : a.val.length = n)
        (h_b_len : b.val.length = n)
        (h_k_pos : 1 ≤ k.val)
        (h_k_le : k.val ≤ (n : ℤ))
        (h_a_bounds : ∀ (i : ℕ) (hi : i < n),
          -(10 ^ 9 : ℤ) ≤ (a.val.get ⟨i, by omega⟩).val ∧ (a.val.get ⟨i, by omega⟩).val ≤ 10 ^ 9)
        (h_b_bounds : ∀ (i : ℕ) (hi : i < n),
          -(10 ^ 9 : ℤ) ≤ (b.val.get ⟨i, by omega⟩).val ∧ (b.val.get ⟨i, by omega⟩).val ≤ 10 ^ 9)
        (h_le : ∀ (i : ℕ) (hi : i < n),
          (a.val.get ⟨i, by omega⟩).val ≤ (b.val.get ⟨i, by omega⟩).val), ∀ r s : Std.I64, max_subarray_sum a k = ok r →
          max_subarray_sum b k = ok s → r.val ≤ s.val) := by
    sorry

  end AegisSpec.MaxSubarraySum
