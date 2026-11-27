import Aegis.MaximumSubarraySum.Code.Funs

/-!
# Specifications of `Aegis.MaximumSubarraySum.maximum_subarray_sum`

LeetCode problem `maximum-sum-of-distinct-subarrays-with-length-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumSubarraySum

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def window (nums : Slice Std.I64) (k s : ℕ) : List Std.I64 := (nums.val.drop s).take k

  def windowPairwiseDistinct (nums : Slice Std.I64) (k s : ℕ) : Prop :=
    ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
      s ≤ i → i < j → j < s + k → (nums.val[i]'hi).val ≠ (nums.val[j]'hj).val

  def admissible (nums : Slice Std.I64) (k : Std.I64) (s : ℕ) : Prop :=
    s + k.val.toNat ≤ nums.val.length ∧ windowPairwiseDistinct nums k.val.toNat s

  def windowSum (nums : Slice Std.I64) (k s : ℕ) : ℤ :=
    (window nums k s).map (fun x => x.val) |>.sum

  def IsWindowMax (nums : Slice Std.I64) (k : ℕ) (W : ℤ) : Prop :=
    (∃ s, s + k ≤ nums.val.length ∧ windowSum nums k s = W) ∧
      ∀ s, s + k ≤ nums.val.length → windowSum nums k s ≤ W

  /-- The function returns a result r. Call a start index s admissible when 0 ≤ s ≤ len(nums)-k and the k entries nums[s], nums[s+1], ..., nums[s+k-1] are pairwise distinct (for all i,j with s ≤ i < j < s+k, nums[i] ≠ nums[j]). For an admissible s let sum(s) = Σ_{t=0}^{k-1} nums[s+t]. If at least one admissible s exists, then r = sum(s*) for some admissible s* and sum(s) ≤ r for every admissible s. If no admissible s exists, then r = 0.
    Preconditions: len(nums) ≥ 1; len(nums) ≤ 100000; 1 ≤ k ≤ len(nums); for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_k_ge : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∃ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r ∧
        ((∃ s, admissible nums k s) →
          ∃ s, admissible nums k s ∧ r.val = windowSum nums k.val.toNat s ∧
            ∀ s', admissible nums k s' → windowSum nums k.val.toNat s' ≤ r.val) ∧
        ((¬ ∃ s, admissible nums k s) → r.val = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_k_ge : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∃ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r ∧
          ((∃ s, admissible nums k s) →
            ∃ s, admissible nums k s ∧ r.val = windowSum nums k.val.toNat s ∧
              ∀ s', admissible nums k s' → windowSum nums k.val.toNat s' ≤ r.val) ∧
          ((¬ ∃ s, admissible nums k s) → r.val = 0)) := by
    sorry

  /-- For every nums and k satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
    Preconditions: len(nums) ≥ 1; len(nums) ≤ 100000; 1 ≤ k ≤ len(nums); for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_k_ge : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∃ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_k_ge : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∃ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r ≥ 0.
    Preconditions: len(nums) ≥ 1; len(nums) ≤ 100000; 1 ≤ k ≤ len(nums); for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_k_ge : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_k_ge : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, either r = 0 or r ≥ k, with k viewed as a natural number.
    Preconditions: len(nums) ≥ 1; len(nums) ≤ 100000; 1 ≤ k ≤ len(nums); for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_k_ge : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
        r.val = 0 ∨ (k.val.toNat : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_k_ge : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
          r.val = 0 ∨ (k.val.toNat : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r ≤ 100000 * k, with k viewed as a natural number.
    Preconditions: len(nums) ≥ 1; len(nums) ≤ 100000; 1 ≤ k ≤ len(nums); for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_k_ge : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
        r.val ≤ 100000 * (k.val.toNat : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_k_ge : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
          r.val ≤ 100000 * (k.val.toNat : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, let W = max{Σ_{t=0}^{k-1} nums[s+t] | 0 ≤ s ≤ len(nums)-k}; then r ≤ W.
    Preconditions: len(nums) ≥ 1; len(nums) ≤ 100000; 1 ≤ k ≤ len(nums); for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_k_ge : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ (r : Std.I64), Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
        ∀ W : ℤ, IsWindowMax nums k.val.toNat W → r.val ≤ W := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_k_ge : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ (r : Std.I64), Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
          ∀ W : ℤ, IsWindowMax nums k.val.toNat W → r.val ≤ W) := by
    sorry

  /-- Whenever the function returns a result r, for every admissible start index s (that is, 0 ≤ s ≤ len(nums)-k and nums[s], ..., nums[s+k-1] are pairwise distinct), we have Σ_{t=0}^{k-1} nums[s+t] ≤ r.
    Preconditions: len(nums) ≥ 1; len(nums) ≤ 100000; 1 ≤ k ≤ len(nums); for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_k_ge : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
        ∀ s, admissible nums k s → windowSum nums k.val.toNat s ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_k_ge : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
          ∀ s, admissible nums k s → windowSum nums k.val.toNat s ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if at least one admissible start index exists (that is, some s with 0 ≤ s ≤ len(nums)-k and nums[s], ..., nums[s+k-1] pairwise distinct), then there exists such an admissible start index s with r = Σ_{t=0}^{k-1} nums[s+t].
    Preconditions: len(nums) ≥ 1; len(nums) ≤ 100000; 1 ≤ k ≤ len(nums); for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_k_ge : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
        (∃ s, admissible nums k s) →
          ∃ s, admissible nums k s ∧ r.val = windowSum nums k.val.toNat s := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_k_ge : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
          (∃ s, admissible nums k s) →
            ∃ s, admissible nums k s ∧ r.val = windowSum nums k.val.toNat s) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there is no start index s with 0 ≤ s ≤ len(nums)-k such that nums[s], ..., nums[s+k-1] are pairwise distinct.
    Preconditions: len(nums) ≥ 1; len(nums) ≤ 100000; 1 ≤ k ≤ len(nums); for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_k_ge : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
        (r.val = 0 ↔ ¬ ∃ s, admissible nums k s) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_k_ge : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
          (r.val = 0 ↔ ¬ ∃ s, admissible nums k s)) := by
    sorry

  /-- For every integer c and every array nums' of the same length as nums such that nums'[i] = nums[i] + c for all i and nums' also satisfies the same bounds with the same k (in particular len(nums') ≤ 100000 and 1 ≤ nums'[i] ≤ 100000), whenever the function returns r on (nums,k) and returns r' on (nums',k): a start index s is admissible for nums exactly when it is admissible for nums' (where admissible means 0 ≤ s ≤ len-k and the length-k block is pairwise distinct); if no admissible start exists then r = r' = 0; if at least one admissible start exists then r' = r + k*c.
    Preconditions: len(nums) ≥ 1; len(nums) ≤ 100000; 1 ≤ k ≤ len(nums); for every i with 0 ≤ i < len(nums), 1 ≤ nums[i] ≤ 100000. -/
  theorem spec_10 (nums nums' : Slice Std.I64) (k : Std.I64) (c : ℤ)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_k_ge : 1 ≤ k.val)
      (h_k_le : k.val ≤ (nums.val.length : ℤ))
      (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (h_shift : vals nums' = (vals nums).map (fun x => x + c))
      (h_len'_le : nums'.val.length ≤ 100000)
      (h_nums' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
      ∀ r r', Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
        Aegis.MaximumSubarraySum.maximum_subarray_sum nums' k = ok r' →
          (∀ s, (admissible nums k s ↔ admissible nums' k s)) ∧
          ((¬ ∃ s, admissible nums k s) → r.val = 0 ∧ r'.val = 0) ∧
          ((∃ s, admissible nums k s) → r'.val = r.val + (k.val.toNat : ℤ) * c) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (c : ℤ)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_k_ge : 1 ≤ k.val)
        (h_k_le : k.val ≤ (nums.val.length : ℤ))
        (h_nums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (h_shift : vals nums' = (vals nums).map (fun x => x + c))
        (h_len'_le : nums'.val.length ≤ 100000)
        (h_nums' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r r', Aegis.MaximumSubarraySum.maximum_subarray_sum nums k = ok r →
          Aegis.MaximumSubarraySum.maximum_subarray_sum nums' k = ok r' →
            (∀ s, (admissible nums k s ↔ admissible nums' k s)) ∧
            ((¬ ∃ s, admissible nums k s) → r.val = 0 ∧ r'.val = 0) ∧
            ((∃ s, admissible nums k s) → r'.val = r.val + (k.val.toNat : ℤ) * c)) := by
    sorry

  end AegisSpec.MaximumSubarraySum
